------------------------- MODULE BookKeeperProtocolUnboundedLedgers -------------------------
EXTENDS MessagePassingUnboundedLedgers, Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
********************************************
            UNBOUNDED LEDGERS
********************************************

This is a modified specification of the BookKeeper protocol that contains the following changes:
1. Built on the changes of the BookKeeperProtocolGuaranteedWriteQuorum spec. This Unbounded
   Ledgers design will only be safe when used in conjunction with "guaranteed write quorum".
   A separate design using terms is required when using the existing behaviour where only
   ack quorum is guaranteed. If you use this design with existing AQ behaviour, there is the
   risk of log divergence between bookies.

2. Ledgers can be written to by any client, but only one client at a time. Just as in the regular
   BookKeeper protocol, it is assumed there is leader election for clients external to the protocol.
   So under normal circumstances, there should only be one client trying to write to the ledger but
   the protocol can cope with two or more clients battling for control.

   Fencing is now based on integer terms rather than a boolean value. When a client decides it should 
   be the one that writes to the ledger it increments the ledger's term both in metadata and across 
   the bookies of the last fragment.

   Recovery is performed now at the beginning of a term, rather than just when closing a ledger.

   The following messages must include the current term of the client:
   - regular add entry requests
   - recovery LAFR read requests
   - recovery read requests
   - recovery add entry requests

   Regular reads do not need a term.

   Bookies include the term of the request when sending the corresponding response. This allows
   the client to discard any responses that do not match their current term.
*)

\* Input parameters
CONSTANTS Bookies,                      \* The bookies available e.g. { B1, B2, B3, B4 }
          Clients,                      \* The clients e.g. {c1, c2}
          WriteQuorum,                  \* The replication factor under normal circumstances
          AckQuorum,                    \* The number of bookies that must confirm an entry for the
                                        \* client to acknowledge to its own client, also the minimum
                                        \* replication factor (can occur in scenarios such as ensemble change or ledger closes)
          SendLimit,                    \* The data items to send. Limited to a very small number of data items
                                        \* in order to keep the state space small. E.g 1 or 2
          InflightLimit                 \* Limit the number of unacknowledged add entry requests by the client
                                        \* which can reduce to state space significantly

\* Model values
CONSTANTS Nil,
          NoSuchEntry,
          Unknown,
          OK,
          NeedMoreResponses,
          InvalidTerm,
          STATUS_OPEN,
          STATUS_IN_RECOVERY,
          STATUS_CLOSED,
          CLIENT_WITHDRAWN,
          RECOVERY_ABORTED

\* Ledger state in the metadata store
VARIABLES meta_status,              \* the ledger status
          meta_fragments,           \* the fragments of the ledger
          meta_last_entry,          \* the endpoint of the ledger (set on closing)
          meta_version,             \* ledger metadata version (incremented on each update)
          meta_term                 \* the current term of the ledger

\* Bookie state (each is a function whose domain is the set of bookies) pertaining to this single ledger
VARIABLES b_entries,                \* the entries stored in each bookie
          b_term,                   \* the term of the ledger on each bookie
          b_lac,                    \* the last add confirmed of the ledger on each bookie
          b_lafr                    \* the last add fully replicated of the ledger on each bookie

\* the state of the clients
VARIABLES clients                   \* the set of BookKeeper clients

ASSUME SendLimit \in Nat
ASSUME SendLimit > 0
ASSUME WriteQuorum \in Nat
ASSUME WriteQuorum > 0
ASSUME AckQuorum \in Nat
ASSUME AckQuorum > 0
ASSUME WriteQuorum >= AckQuorum

bookie_vars == << b_term, b_entries, b_lac, b_lafr >>
meta_vars == << meta_term, meta_status, meta_fragments, meta_last_entry, meta_version >>
vars == << bookie_vars, clients, meta_vars, messages >>

(***************************************************************************)
(* Recovery Phases                                                         *)
(***************************************************************************)
NotStarted == 0
FencingPhase == 1
ReadWritePhase == 2

(***************************************************************************)
(* Records                                                                 *)
(***************************************************************************)

EntryIds ==
    1..SendLimit

NilEntry == [id |-> 0, data |-> Nil]

Entry ==
    [id: EntryIds, data: EntryIds \union {Nil}]

\* The id field is just a way of knowing its ordinal position in the list 
\* of fragments rather than it being an actual identifier. Its not part of
\* the protocol, just a convenience for this spec.
Fragment ==
    [id: Nat, ensemble: SUBSET Bookies, first_entry_id: Nat]

PendingAddOp ==
    [entry: Entry, fragment_id: Nat, ensemble: SUBSET Bookies]

ClientStatuses ==
    {Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED, CLIENT_WITHDRAWN}
    
ReadResponses ==
    { OK, NoSuchEntry, Unknown } 

ClientState ==
    [id: Clients,
     meta_version: Nat \union {Nil},            \* The metadata version this client has
     status: ClientStatuses,                    \* The possible statuses of a client
     term: Nat,                                 \* The possible terms
     fragments: [Nat -> Fragment],              \* The fragments of the ledger known by the client
     curr_fragment: Fragment \union {Nil},      \* The current fragment known by a client
     pending_add_ops: SUBSET PendingAddOp,      \* The pending add operations of a client
     lap: Nat,                                  \* The Last Add Pushed of a client
     lac: Nat,                                  \* The Last Add Confirmed of a client
     lafr: Nat,                                 \* The Last Add Fully Replicated of a client
     confirmed: [EntryIds -> SUBSET Bookies],   \* The bookies that have confirmed each entry id
     fenced: SUBSET Bookies,                    \* The bookies that have confirmed to this client that they have incremented the term
     \* ledger recovery only
     recovery_ensemble: SUBSET Bookies,         \* The ensemble of the last fragment at the beginning of recovery
                                                \* where all read recovery requests are sent
     curr_read_entry: Entry \union {Nil},       \* The entry currently being read (during recovery)
     read_responses: SUBSET ReadResponses,      \* The recovery read responses of the current entry
     recovery_phase: 0..ReadWritePhase,         \* The recovery phases
     last_recoverable_entry: Nat \union {Nil}]  \* The last recoverable entry set to the lowest negative
                                                \* recovery read - 1 

\* Each client starts empty, no state
InitClient(cid) ==
    [id                     |-> cid,
     meta_version           |-> Nil,
     status                 |-> Nil,
     term                   |-> 0,
     curr_fragment          |-> Nil,
     fragments              |-> <<>>,
     pending_add_ops        |-> {},
     lap                    |-> 0,
     lac                    |-> 0,
     lafr                   |-> 0,
     confirmed              |-> [id \in EntryIds |-> {}],
     fenced                 |-> {},
     recovery_ensemble      |-> {},
     curr_read_entry        |-> Nil,
     read_responses         |-> {},
     recovery_phase         |-> 0,
     last_recoverable_entry |-> Nil]

(***************************************************************************)
(* Fragment Helpers                                                        *)
(***************************************************************************)

FragmentOf(fragment_id, fragments) ==
    fragments[fragment_id]

FragmentOfEntryId(entry_id, fragments) ==
    IF Len(fragments) = 1
    THEN fragments[1]
    ELSE IF Last(fragments).first_entry_id <= entry_id
         THEN Last(fragments)
         ELSE
            LET f_id == CHOOSE f1 \in DOMAIN fragments :
                            \E f2 \in DOMAIN fragments :
                                /\ fragments[f1].id = fragments[f2].id-1
                                /\ fragments[f1].first_entry_id <= entry_id
                                /\ fragments[f2].first_entry_id > entry_id
            IN fragments[f_id]

ValidEnsemble(ensemble, include_bookies, exclude_bookies) ==
    /\ Cardinality(ensemble) = WriteQuorum
    /\ ensemble \intersect exclude_bookies = {}
    /\ include_bookies \intersect ensemble = include_bookies
    /\ \A i \in DOMAIN meta_fragments : ensemble # meta_fragments[i].ensemble

EnsembleAvailable(include_bookies, exclude_bookies) ==
    \E ensemble \in SUBSET Bookies :
        ValidEnsemble(ensemble, include_bookies, exclude_bookies)

SelectEnsemble(include_bookies, exclude_bookies) ==
    CHOOSE ensemble \in SUBSET Bookies :
        ValidEnsemble(ensemble, include_bookies, exclude_bookies)
        
(***************************************************************************
QuorumCoverage

Quorum coverage is a quorum that is required in two places in the       
protocol:                                                               
 - LAFR fencing requests must have been confirmed by enough bookies 
   such that there exists no ack quorum of bookies in the current 
   ledger ensemble that remain unfenced.                                                             
 - An entry is only unrecoverable when there is no ack quorum of bookies 
   of the entry ensemble that have or could confirm they have the entry. 

This can be expressed in different ways:                                
 - There exists no ack quorum of bookies within the cohort that don't    
   satisfy the property.                                                 
 - In every ack quorum of bookies of the cohort, at least one bookie     
   must satisfy the property.                                                       

It can also simply be distilled down to (Cohort size - AckQuorum) + 1  
bookies must satisfy the property.  
For fencing, the cohort is the current fragment ensemble. For recovery
reads, it is the writeset of the entry. The writeset of the entry is
the set of bookies that metadata say must host the bookie. When the ensemble
size = Write Quorum then the writeset = the current ensemble.
***************************************************************************)

HasQuorumCoverage(s, cohort_size) ==
    Cardinality(s) >= ((cohort_size - AckQuorum) + 1)

(***************************************************************************
ACTION: A bookie rejects a stale request

A bookie will reject any request that has a term lower than its own.
****************************************************************************)

GetRejectOtherResponse(msg, type) ==
    [type     |-> type,
     bookie   |-> msg.bookie,
     cid      |-> msg.cid,
     term     |-> msg.term,
     code     |-> InvalidTerm]

GetRejectAddResponse(msg) ==
    [type     |-> AddEntryResponseMessage,
     bookie   |-> msg.bookie,
     cid      |-> msg.cid,
     entry    |-> msg.entry,
     term     |-> msg.term,
     code     |-> InvalidTerm]

GetRejectMessage(msg) ==
    CASE msg.type = AddEntryRequestMessage -> GetRejectAddResponse(msg)
      [] msg.type = FenceRequestMessage -> GetRejectOtherResponse(msg, FenceResponseMessage)
      [] msg.type = ReadRequestMessage -> GetRejectOtherResponse(msg, ReadResponseMessage)
     
BookieRejectsRequest ==
    \E msg \in DOMAIN messages :
        /\ ReceivableRequest(messages, msg)
        /\ \/ /\ msg.type = AddEntryRequestMessage
              /\ IsEarliestAdd(msg)
           \/ msg.type # AddEntryRequestMessage
        /\ b_term[msg.bookie] > msg.term
        /\ ProcessedOneAndSendAnother(msg, GetRejectMessage(msg))
        /\ UNCHANGED << bookie_vars, clients, meta_vars >>      

(***************************************************************************
ACTION: A client withdraws due to having a stale term

If a client receives an InvalidTerm response then it must cease activity.
It could reengage after checking the ledger metadata and getting the up to
date term, but in this spec the client simply stops. We don't need to model
reengagement explicitly as we already get this from supporting multiple clients,
though you would need at least 3 clients.   
****************************************************************************)

ClientWithdraws ==
    \E msg \in DOMAIN messages :
        /\ ReceivableResponse(messages, msg)
        /\ \/ /\ msg.type = AddEntryResponseMessage
              /\ IsEarliestAdd(msg)
           \/ msg.type # AddEntryResponseMessage
        /\ msg.code = InvalidTerm
        /\ clients' = [clients EXCEPT ![msg.cid] = 
                                    [@ EXCEPT !.status = CLIENT_WITHDRAWN,
                                              !.meta_version = Nil]]
        /\ MessageProcessed(msg)
        /\ UNCHANGED << bookie_vars, meta_vars >>
        
(***************************************************************************
ACTION: Create ledger                                                   
                                                                         
A ledger is created by a client. This is a metadata only operation where an
ensemble (the bookies that will host the first fragment) is selected 
non-deterministically and the status is set to OPEN.                                                  
****************************************************************************)

ClientCreatesLedger(cid) ==
    /\ meta_status = Nil
    /\ clients[cid].meta_version = Nil
    /\ LET fragment == [id |-> 1, ensemble |-> SelectEnsemble({},{}), first_entry_id |-> 1]
       IN
        /\ clients' = [clients EXCEPT ![cid] = 
                                [@ EXCEPT !.status        = STATUS_OPEN,
                                          !.meta_version  = 1,
                                          !.term          = 1,
                                          !.fragments     = Append(meta_fragments, fragment),
                                          !.curr_fragment = fragment]]
        /\ meta_status' = STATUS_OPEN
        /\ meta_term' = 1
        /\ meta_version' = 1
        /\ meta_fragments' = Append(meta_fragments, fragment)
    /\ UNCHANGED << bookie_vars, meta_last_entry, messages >>

(**************************************************************************
ACTION: Send Add Entry Requests                                         
                                                                         
The client that created the ledger sends an AddEntryRequestMessage to
each bookie of the current fragment ensemble. The data sent can be an 
arbitrary byte array but in this spec it is simply an integer that 
increases by one on each send, forming a sequence (1,2,3 etc).

Key points:
- Each request includes the current LAC of the client. The LAC is stored
  alongside the ledger id, entry id and entry body in each bookie.          
- Periodically the LAFR can be included.
- the current term of the client must be included in writes.
***************************************************************************)

GetAddEntryRequests(c, entry, ensemble) ==
    { [type     |-> AddEntryRequestMessage,
       bookie   |-> b,
       cid      |-> c.id,
       entry    |-> entry,
       lac      |-> c.lac,
       lafr     |-> c.lafr,
       term     |-> c.term] : b \in ensemble }

SendAddEntryRequests(c, entry) ==
    /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                  entry,
                                                  c.curr_fragment.ensemble))
    /\ clients' = [clients EXCEPT ![c.id] =  
                                [c EXCEPT !.lap = entry.id,
                                          !.pending_add_ops = @ \union 
                                               {[entry       |-> entry,
                                                 fragment_id |-> c.curr_fragment.id,
                                                 ensemble    |-> c.curr_fragment.ensemble]}]]

ClientSendsAddEntryRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_OPEN
        /\ c.lap - c.lac <= InflightLimit - 1 \* configurable state space reduction
        /\ LET entry_data == c.lap + 1
           IN
            /\ entry_data <= SendLimit
            /\ SendAddEntryRequests(c, [id   |-> entry_data, data |-> entry_data])
        /\ UNCHANGED << bookie_vars, meta_vars >>

(**************************************************************************
ACTION: A bookie receives an AddEntryRequestMessage, sends a confirm.   
                                                                         
A bookie receives a AddEntryRequestMessage. Either the add request is a
recovery add request or the ledger is not fenced so it adds the entry and  
responds with a success response.

Key points:
- add requests (whether they are recovery requests or not) are only accepted
  if the term of the ledger on that bookie is equal to or lower than the request
  term.
- if the bookie term is lower, then it updates its term to the term of the request.  
***************************************************************************)

GetAddEntryResponse(add_entry_msg) ==
    [type     |-> AddEntryResponseMessage,
     bookie   |-> add_entry_msg.bookie,
     cid      |-> add_entry_msg.cid,
     entry    |-> add_entry_msg.entry,
     term     |-> add_entry_msg.term,
     code     |-> OK]

BookieSendsAddConfirmedResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ IsEarliestAdd(msg)
        /\ b_term[msg.bookie] <= msg.term
        /\ b_term' = [b_term EXCEPT ![msg.bookie] = msg.term]
        /\ b_entries' = [b_entries EXCEPT ![msg.bookie] = @ \union {msg.entry}]
        /\ b_lac' = [b_lac EXCEPT ![msg.bookie] = IF msg.lac > @ THEN msg.lac ELSE @]
        /\ b_lafr' = [b_lafr EXCEPT ![msg.bookie] = IF msg.lafr > @ THEN msg.lafr ELSE @]
        /\ ProcessedOneAndSendAnother(msg, GetAddEntryResponse(msg))
        /\ UNCHANGED << clients, meta_vars >>

(***************************************************************************
ACTION: A client receive a success AddEntryResponseMessage              

A client receives a success AddEntryResponseMessage and adds the bookie 
to the list of bookies that have acknowledged the entry.                
It may also:                                                            
 - advance the LAC.
 - advance the LAFR.                          
 - remove pending add ops that are equal to or lower than the new LAFR    

Key points:
- When the LAC is advanced, it advances to the highest entry that:
    1. has reached Ack Quorum
    2. ALL prior entries have also reached ack quorum.
- When the LAFR is advanced, it advances to the highest entry that:
    1. has reached Write Quorum
    2. ALL prior entries have also reached write quorum.
- Implicit in this spec is that once the LAC is advanced, any entries it
  passes or reaches is acknowledged back to the caller.
- Only remove an entries when they have reached WQ and their entire prefix
  has also reached WQ.
****************************************************************************)

AddToConfirmed(c, entry_id, bookie) ==
    [c.confirmed EXCEPT ![entry_id] = @ \union {bookie}]

\* Only remove if it has reached the Ack Quorum and <= LAC
UpdatedPendingAddOps(c, lwq) ==
    { op \in c.pending_add_ops : op.entry.id > lwq }

\* choose an entry that reached the desired quorum and whose entire prefix
\* has also reached that quorum. Note, we need the "if exists" first else
\* choose will fail if there is no such entry. 
MaxContiguousEntryAtQuorum(confirmed, quorum) ==
    IF \E id \in DOMAIN confirmed : \A id1 \in 1..id :
                                        Cardinality(confirmed[id1]) >= quorum
    THEN 
        CHOOSE id \in DOMAIN confirmed : 
            /\ \A id1 \in 1..id : Cardinality(confirmed[id1]) >= quorum
            /\ ~\E other_id \in DOMAIN confirmed :
                /\ other_id > id 
                /\ \A other_id1 \in 1..other_id : Cardinality(confirmed[other_id1]) >= quorum
    ELSE 0       

ReceiveAddConfirmedResponse(c) ==
    \E msg \in DOMAIN messages :
        /\ msg.cid = c.id
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestAdd(msg)
        /\ msg.code = OK
        /\ msg.bookie \in c.curr_fragment.ensemble
        /\ LET confirmed == AddToConfirmed(c, msg.entry.id, msg.bookie)
           IN LET lac  == MaxContiguousEntryAtQuorum(confirmed, AckQuorum)
                  lafr == MaxContiguousEntryAtQuorum(confirmed, WriteQuorum)
              IN
                clients' = [clients EXCEPT ![c.id] = 
                                        [c EXCEPT !.confirmed       = confirmed,
                                                  !.lac             = IF lac > @ THEN lac ELSE @,
                                                  !.lafr            = IF lafr > @ THEN lafr ELSE @,
                                                  !.pending_add_ops = UpdatedPendingAddOps(c, lafr)]]
        /\ MessageProcessed(msg)


ClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ ReceiveAddConfirmedResponse(clients[cid])
    /\ UNCHANGED << bookie_vars, meta_vars >>

RecoveryClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ReceiveAddConfirmedResponse(clients[cid])
    /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************
ACTION: A client performs an ensemble change.                           

One or more writes to a bookie has failed and in order for the client 
to be able to continue making progress a new fragment must be created with
replacement bookies for those that had error responses.

In this spec the only write failure is a timeout. Fenced responses do
not cause ensemble changes.
          
The client:                                                             
 - opens a new fragment with a new ensemble, with its first entry id    
   being LAFR + 1.
 - the failed bookie is removed from the confirmed set of any pending add ops.
   For entries that have Ack Quorum but are ahead of the LAC, and therefore 
   not committed, this can reduce them back down to below AckQuorum.
 - if the lowest uncommitted entry id is the same as the current fragment,
   then the current fragment gets overwritten, else a new fragment is
   appended.                                             
 - If not enough bookies are available to form a new ensemble then writes
   cannot continue. With unbounded ledgers, the ledger is not closed at this
   point but instead either the client waits and tries again or disengages.

NOTE: Before triggering another ensemble change, we ensure that all    
      pending add ops that need to be sent to bookies due to a prior   
      ensemble change, do get sent first. This is a state space reduction
      measure.

Key points:
- There will be pending add ops that must now be sent to the replacement
  bookie(s). This is performed in the actions ClientResendsPendingAddOp
  and RecoveryClientSendsPendingAddOp.
- when the client changes the ensemble of an OPEN ledger, it immediately updates
  the metadata in the metadata store. It cannot progress until the metadata
  is updated.
- when a client changes the ensemble of an IN_RECOVERY ledger 
  it DOES NOT commit updates to the metadata immediately. Instead it waits until
  the read/write phase is complete and then updates the ensembles when it
  sets the status to OPEN. Committing metadata changes during recovery is unsafe
  for two reasons:
  1. if recovery fails and needs to be retried, the last fragment will be
     different now and some bookies may never have seen the entries, causing
     ledger truncation.
  2. if two clients attempt recovery concurrently, they can affect each other
     by changing the fragments so they direct recovery reads to bookies that
     were not in the original fragment and therefore cause ledger truncation.
- All entries, starting at the lowest entry that has not reached WQ is moved
  into the next fragment.
- Bookies that are in the ack set of a pending add op that is committed are 
  pinned. Pinned bookies cannot be replaced in ensemble changes. Any write
  failures to pinned bookies must be delayed until the relevant committed
  have reached WQ.
****************************************************************************)

\* if the lowest entry brought forward is higher than the LAC then no bookies
\* can be pinned. If the bookie is in the confirmed set of a committed entry
\* that is being brought into the next fragment, then it is pinned.
BookiePinned(c, bookie, first_entry_id) ==
    IF first_entry_id > c.lac
    THEN FALSE
    ELSE \E e \in first_entry_id..c.lac :
            bookie \in c.confirmed[e]

NoPendingResends(c) ==
    ~\E op \in c.pending_add_ops :
        /\ \/ op.fragment_id # c.curr_fragment.id
           \/ op.ensemble # c.curr_fragment.ensemble

\* The next fragment is only valid if it's first_entry_id is equal to or higher than all existing fragments.
ValidNextFragment(first_entry_id) ==
    ~\E i \in DOMAIN meta_fragments : meta_fragments[i].first_entry_id > first_entry_id

\* if there already exists an ensemble with the same first_entry_id then replace it,
\* else append a new fragment
UpdatedFragments(c, first_entry_id, new_ensemble) ==
    IF first_entry_id = c.curr_fragment.first_entry_id
    THEN [index \in DOMAIN c.fragments |-> IF c.fragments[index] = Last(c.fragments)
                                              THEN [c.fragments[index] EXCEPT !.ensemble = new_ensemble]
                                              ELSE c.fragments[index]]
    ELSE Append(c.fragments, [id             |-> Len(c.fragments)+1,
                              ensemble       |-> new_ensemble,
                              first_entry_id |-> first_entry_id])

ChangeEnsemble(c, recovery) ==
    /\ NoPendingResends(c)
    /\ \/ recovery
       \/ ~recovery /\ c.meta_version = meta_version
    /\ \E failed_bookies \in SUBSET c.curr_fragment.ensemble :
        /\ \A bookie \in failed_bookies : WriteTimeoutForBookie(messages, c.id, bookie, c.term)
        /\ EnsembleAvailable(c.curr_fragment.ensemble \ failed_bookies, failed_bookies)
        /\ LET first_entry_id == c.lafr + 1
           IN
              /\ \A bookie \in failed_bookies : ~BookiePinned(c, bookie, first_entry_id)
              /\ LET new_ensemble   == SelectEnsemble(c.curr_fragment.ensemble \ failed_bookies, failed_bookies)
                     updated_fragments == UpdatedFragments(c, first_entry_id, new_ensemble)
                 IN
                    \* only update the metadata if not in ledger recovery
                    /\ IF recovery 
                       THEN UNCHANGED << meta_version, meta_fragments >>
                       ELSE /\ meta_fragments' = updated_fragments
                            /\ meta_version' = meta_version + 1
                    /\ clients' = [clients EXCEPT ![c.id] =  
                                        [c EXCEPT !.meta_version  = IF recovery THEN @ ELSE meta_version + 1,
                                                  !.confirmed     = [id \in DOMAIN c.confirmed |->
                                                                       IF id >= first_entry_id
                                                                       THEN c.confirmed[id] \ failed_bookies
                                                                       ELSE c.confirmed[id]],
                                                  !.fragments     = updated_fragments,
                                                  !.curr_fragment = Last(updated_fragments)]]
                    /\ ClearWriteTimeout(c.id, failed_bookies, c.term)

ClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ ChangeEnsemble(clients[cid], FALSE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_term, meta_last_entry >>

RecoveryClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ meta_status = STATUS_IN_RECOVERY
    /\ ChangeEnsemble(clients[cid], TRUE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_term, meta_last_entry >>

(***************************************************************************
ACTION: Client resends a Pending Add Op                                 

A pending add op needs to be sent to one or more bookies of a           
new/updated fragment due to a previous bookie write failure.                    
We resend a pending add op when it has a different fragment id           
or different ensemble to the current fragment. This happens after
an ensemble change has occurred while there are still uncommitted
entries pending more add responses. 
  
The ensemble change may have been a replacement rather than appended    
so the id may be the same but the ensemble different, hence checking    
both.                                                                   
****************************************************************************)

NeedsResend(op, curr_fragment) ==
    \/ op.fragment_id # curr_fragment.id
    \/ op.ensemble # curr_fragment.ensemble

\* update the pending add op ensemble
SetNewEnsemble(c, pending_op) ==
    {
        IF op = pending_op
        THEN [entry       |-> op.entry,
              fragment_id |-> c.curr_fragment.id,
              ensemble    |-> c.curr_fragment.ensemble]
        ELSE op : op \in c.pending_add_ops
    }

\* resend an add to any bookies in the new ensemble that are not in the original
\* then update the op with the new ensemble.
ResendPendingAddOp(c) ==
    /\ \E op \in c.pending_add_ops :
        /\ NeedsResend(op, c.curr_fragment)
        /\ ~\E op2 \in c.pending_add_ops :
            /\ op2.fragment_id = op.fragment_id
            /\ op2.ensemble = op.ensemble
            /\ op2.entry.id < op.entry.id
        /\ LET new_bookies == c.curr_fragment.ensemble \ op.ensemble
           IN
              /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                            op.entry,
                                                            new_bookies))
              /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.pending_add_ops = SetNewEnsemble(c, op)]]

ClientResendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ ResendPendingAddOp(clients[cid])
    /\ UNCHANGED << bookie_vars, meta_vars >>

RecoveryClientSendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ResendPendingAddOp(clients[cid])
    /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************
ACTION: The client of the current term closes the ledger.                                 

The client of the current term decides to close its ledger. The metadata store still        
has the ledger as OPEN and the version matches so the close succeeds.                           
A close can be performed at any time.

Key points:
- the client can only close a ledger once all pending add ops are completed
  (meaning they have reached WQ). If any write fails then ensemble changes
  will occur until the entry reached WQ.
- a client can only close if the metadata version match.
***************************************************************************)

ClientClosesLedgerSuccess(cid) ==
    LET c == clients[cid]
    IN
        /\ c.meta_version = meta_version
        /\ c.status = STATUS_OPEN
        /\ c.term = meta_term
        /\ meta_status = STATUS_OPEN
        /\ Cardinality(c.pending_add_ops) = 0
        /\ clients' = [clients EXCEPT ![cid] = 
                            [@ EXCEPT !.meta_version = @ + 1,
                                      !.status = STATUS_CLOSED]]
        /\ meta_status' = STATUS_CLOSED
        /\ meta_last_entry' = clients[cid].lac
        /\ meta_version' = meta_version + 1
        /\ UNCHANGED << bookie_vars, meta_term, meta_fragments, messages >>

(***************************************************************************
ACTION: A client fails to close the ledger.                         

The client of the current term decides to close its ledger. The metadata store 
version does not match so the close fails and the client ceases further     
interactions with this ledger. In reality the client could reengage but
as mentioned earlier we don't explicitly model that (use >= 3 clients). 
****************************************************************************)

ClientClosesLedgerFail(cid) ==
    LET c == clients[cid]
    IN 
        /\ c.status = STATUS_OPEN
        /\ \/ meta_status # STATUS_OPEN
           \/ c.term # meta_term
           \/ c.meta_version # meta_version
        /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN,
                                                         !.meta_version = Nil]]
        /\ UNCHANGED << bookie_vars, meta_vars, messages >>

(***************************************************************************
ACTION: A client starts a new term.

A client decides it should take over writing to the ledger. 
It changes the meta status to IN_RECOVERY, increments the term and sends 
a fencing read LAFR request to each bookie in the current ensemble.

Key points:
- why a client takes over is outside of this the scope of spec 
  and from a correctness point of view, irrelevant.
****************************************************************************)

GetFencedReadLafrRequests(c, ensemble, new_term) ==
    { [type   |-> FenceRequestMessage,
       bookie |-> bookie,
       cid    |-> c.id,
       term   |-> new_term] : bookie \in ensemble }

ClientStartsNewTerm(cid) ==
    /\ clients[cid].status = Nil
    /\ meta_status \in {STATUS_OPEN, STATUS_IN_RECOVERY}
    /\ meta_status' = STATUS_IN_RECOVERY
    /\ meta_version' = meta_version + 1
    /\ meta_term' = meta_term + 1
    /\ clients' = [clients EXCEPT ![cid] =
                            [@ EXCEPT !.status            = STATUS_IN_RECOVERY,
                                      !.meta_version      = meta_version + 1,
                                      !.term              = meta_term + 1,
                                      !.recovery_phase    = FencingPhase,
                                      !.fragments         = meta_fragments,
                                      !.curr_fragment     = Last(meta_fragments),
                                      !.recovery_ensemble = Last(meta_fragments).ensemble]]
    /\ SendMessagesToEnsemble(GetFencedReadLafrRequests(clients[cid], Last(meta_fragments).ensemble, meta_term + 1))
    /\ UNCHANGED << bookie_vars, meta_fragments, meta_last_entry >>

(***************************************************************************
ACTION: A bookie receives a fencing LAFR request, sends a response.       

A bookie receives a fencing read LAFR request and sends back a success   
response with its LAFR.

Key points:
- fencing works even if the bookie has never seen this ledger. If a bookie
  hasn't seen a ledger, it still fences it (setting the ledger term). 
  If it ignores fencing requests for ledgers it doesn't know about it, 
  we lose correctness as the bookie is a member of the current fragment and 
  if it ignores a fence request then a client of a previous term could in the 
  future still write to it.                  
****************************************************************************)

GetFencingReadLafrResponseMessage(msg) ==
    [type   |-> FenceResponseMessage,
     bookie |-> msg.bookie,
     cid    |-> msg.cid,
     lafr   |-> b_lafr[msg.bookie],
     term   |-> msg.term,
     code   |-> OK]

BookieSendsFencingReadLafrResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, FenceRequestMessage)
        /\ b_term[msg.bookie] <= msg.term
        /\ b_term' = [b_term EXCEPT ![msg.bookie] = msg.term]
        /\ ProcessedOneAndSendAnother(msg, GetFencingReadLafrResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, b_lafr, clients, meta_vars >>

(***************************************************************************
ACTION: A recovery client receives an LAFR fence response                                        

A client receives a success FenceResponseMessage               
and takes note of the bookie that confirmed its fenced status and if    
its LAFR is highest, stores it.                                          
Once the read/write phase has started any late arriving LAFR reads are ignored.

Key points:
- The LAFR of the bookies can be stale but that is ok. The discovering the LAFR
  is just an optimization to avoid having to read all entries starting at the 
  beginning of the current fragment. We don't care about any fragments prior 
  to the current one as we know those were committed.
- we start at LAFR + 1
- we include the term of the client in the requests
****************************************************************************)

ClientReceivesFencingReadLafrResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.recovery_phase = FencingPhase \* we can ignore any late responses after 
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, FenceResponseMessage)
            /\ msg.term = c.term
            /\ msg.code = OK
            /\ LET lafr == IF msg.lafr > c.curr_fragment.first_entry_id - 1
                           THEN msg.lafr
                           ELSE c.curr_fragment.first_entry_id - 1
               IN
                /\ clients' = [clients EXCEPT ![cid] = 
                                    [@ EXCEPT !.fenced = @ \union {msg.bookie},
                                              !.lafr = IF lafr > @ THEN lafr ELSE @,
                                              !.lac = IF lafr > @ THEN lafr ELSE @,
                                              !.lap = IF lafr > @ THEN lafr ELSE @]]
            /\ MessageProcessed(msg)
            /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************
ACTION: A client sends a recovery read request to each bookie.   

A client sends a recovery ReadRequestMessage to each bookie of the    
recovery read ensemble. The client keeps reading until it reaches the
last recoverable entry.                          

Key points:
- The client starts the read/write phase once the bookies that 
  have confirmed they are fenced (set the new term) reaches quorum coverage with the 
  cohort as the current fragment ensemble. See more about quorum coverage
  near the top of the spec.
- It is important to remember that recovery reads get sent to the         
  ensemble of the last fragment ensemble at the time recovery started 
  (called the recovery read ensemble in this spec).
  If reads get sent to the recovery clients current fragment ensemble 
  then ensemble changes resulting from recovery writes can cause reads 
  to be sent to bookies that do not have the entries and the result
  could be ledger truncation.
- recovery read requests also include the term. This is necessary for
  correctness as the fencing LAC requests only prevent new entries from
  reaching Ack Quorum. Entries that are already half written to the ensemble
  can sneak through if we also don't include the term on recovery reads.
****************************************************************************)

GetRecoveryReadRequests(c, entry_id, ensemble) ==
    { [type     |-> ReadRequestMessage,
       bookie   |-> b,
       cid      |-> c.id,
       entry_id |-> entry_id,
       term     |-> c.term] : b \in ensemble }

ClientSendsRecoveryReadRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ \/ /\ c.recovery_phase = ReadWritePhase
              /\ c.last_recoverable_entry = Nil
              /\ c.curr_read_entry = Nil
           \/ /\ c.recovery_phase = FencingPhase
              /\ HasQuorumCoverage(c.fenced, Cardinality(c.recovery_ensemble)) 
        /\ LET next_entry_id == c.lap+1
           IN
            /\ clients' = [clients EXCEPT ![c.id] = [c EXCEPT !.recovery_phase  = ReadWritePhase,
                                                              !.curr_read_entry = next_entry_id,
                                                              !.fenced          = {}]] \* fenced no longer needed to reset
            /\ SendMessagesToEnsemble(GetRecoveryReadRequests(c, next_entry_id, c.recovery_ensemble))
            /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************
ACTION: A bookie receives a recovery read request, sends a response.              

A bookie receives a ReadRequestMessage and sends back a success         
response if it has the entry and a non-success if it doesn't.           

Key points:
- Ledger term in the bookies must be equal to or lower than the request term.
- If the bookie ledger term is lower, it updates it.
****************************************************************************)

GetReadResponseMessage(msg) ==
    [type     |-> ReadResponseMessage,
     bookie   |-> msg.bookie,
     cid      |-> msg.cid,
     entry    |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN CHOOSE entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  ELSE [id |-> msg.entry_id, data |-> Nil],
     term     |-> msg.term,
     code     |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN OK
                  ELSE NoSuchEntry]

BookieSendsReadResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadRequestMessage)
        /\ b_term[msg.bookie] <= msg.term
        /\ b_term' = [b_term EXCEPT ![msg.bookie] = msg.term]
        /\ ProcessedOneAndSendAnother(msg, GetReadResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, b_lafr, clients, meta_vars >>

(***************************************************************************
ACTION: Client receives a recovery read response.                                
                                                                         
On receiving each response, the client must decide whether     
the entry is recoverable, non-recoverable or needs more responses to    
decide. In order to balance performance with safety, the client is      
generous with positive results (only requires one positive read to      
treat an entry as recoverable) but strict on negative results (requires 
quorum coverage of NoSuchEntry responses to treat an entry as           
unrecoverable).                                                         

If the entry is recoverable then the entry is added to the list of     
pending add ops that will be subsequently sent to the current fragment
ensemble.                      

If the entry is unrecoverable, then the read phase is complete and
recovery continues until all recovery writes are complete.         

If all responses for a given entry have been received and still neither 
the positive threshold of 1 nor the negative threshold of quorum 
coverage (WQ-AQ)+1 has been reached, the final result of the read 
is Unknown, and the ledger recovery is aborted.                                 
****************************************************************************)

ReadStatus(c, responses) ==
    IF \E msg \in responses : msg.code = OK 
    THEN OK \* generous on positive results
    ELSE \* strict on negative
         IF HasQuorumCoverage({msg \in responses : msg.code = NoSuchEntry }, WriteQuorum)
         THEN NoSuchEntry
         ELSE \* all responses in and neither positive nor negative threshold reached
              IF Cardinality(responses) 
                + ReadTimeoutCount(c.id, c.recovery_ensemble, c.term) = WriteQuorum
              THEN Unknown
              ELSE NeedMoreResponses

ReadPositive(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                        [c EXCEPT !.curr_read_entry = Nil, \* reset for next read
                                  !.read_responses  = {},  \* reset for next read
                                  !.lap             = @ + 1,
                                  !.pending_add_ops = @ \union {[entry       |-> [id   |-> c.lap + 1,
                                                                                  data |-> msg.entry.data],
                                                                 fragment_id |-> c.curr_fragment.id,
                                                                 ensemble    |-> c.curr_fragment.ensemble]}]]
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble, c.term)
      
ReadNegative(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.curr_read_entry        = Nil, \* reset to reduce state space
                              !.read_responses         = {},  \* reset to reduce state space
                              !.recovery_ensemble      = {},  \* reset to reduce state space
                              !.last_recoverable_entry = msg.entry.id - 1]]
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble, c.term)
    
ReadUnknown(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.status = RECOVERY_ABORTED,
                              !.curr_read_entry   = Nil, \* reset to reduce state space
                              !.read_responses    = {},  \* reset to reduce state space
                              !.recovery_ensemble = {}]] \* reset to reduce state space
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble, c.term)
    
NotEnoughReadResponses(c, msg, responses) ==
    clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.read_responses = responses]]    
    
ClientReceivesRecoveryReadResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.status = STATUS_IN_RECOVERY
       /\ c.recovery_phase = ReadWritePhase
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ msg.term = c.term
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
            /\ msg.code = OK
            /\ msg.entry.id = c.curr_read_entry \* we can ignore any responses not of the current read
            /\ LET read_responses == c.read_responses \union {msg}
                   read_status == ReadStatus(c, read_responses)
               IN
                  /\ CASE read_status = OK -> ReadPositive(c, msg, read_responses)
                      [] read_status = NoSuchEntry -> ReadNegative(c, msg, read_responses)
                      [] read_status = Unknown -> ReadUnknown(c, msg, read_responses)
                      [] read_status = NeedMoreResponses -> NotEnoughReadResponses(c, msg, read_responses)
                  /\ MessageProcessed(msg)
            /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************
ACTION: Client writes back a entry that was successfully read.          
                                                                         
Recovery writes follow the same logic as replication writes, in that    
they can involve the creation of new fragments. Also note that all      
entries are written to the current fragment, not necessarily the        
fragment they were read from (recovery_ensemble).

Key points:
- The term must be included to prevent clients of previous terms from also
  attempting recovery.
****************************************************************************)

NotSentWrite(c, op) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = AddEntryRequestMessage
        /\ msg.cid = c.id
        /\ msg.entry = op.entry
        /\ msg.term = c.term

ClientWritesBackEntry(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ c.recovery_phase = ReadWritePhase
        /\ \E op \in c.pending_add_ops :
            /\ NotSentWrite(c, op)
            /\ ~\E op2 \in c.pending_add_ops :
                /\ NotSentWrite(c, op2)
                /\ op2.entry.id < op.entry.id
            /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                          op.entry,
                                                          c.curr_fragment.ensemble))
        /\ UNCHANGED << bookie_vars, clients, meta_vars >>

(***************************************************************************
ACTION: Client changes the ledger status to OPEN.                              

Once all the entries that were read during recovery have been           
successfully written back, recovery is complete. The final action is to
update the metadata:        
 - status to OPEN                                                      
 - the fragments (which may have changed due to ensemble changes during  
   recovery)
   
Key points:
- The client is only able to change the ledger to OPEN if the metadata store 
  still has the ledger status as IN_RECOVERY and has the same metadata version 
  as the client. Else the metadata cannot be updated and the recovery is
  aborted.
- Recovery is only complete once all pending add ops are completed
  (meaning they have reached WQ).
****************************************************************************)

ClientChangesTermToOpen(cid) ==
    LET c == clients[cid]
    IN
        /\ meta_version = c.meta_version
        /\ meta_status = STATUS_IN_RECOVERY
        /\ c.status = STATUS_IN_RECOVERY
        /\ c.recovery_phase = ReadWritePhase
        /\ c.last_recoverable_entry # Nil
        /\ Cardinality(c.pending_add_ops) = 0
        /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.status                 = STATUS_OPEN,
                                          !.meta_version           = @ + 1,
                                          !.last_recoverable_entry = 0,
                                          !.recovery_phase         = NotStarted]]
        /\ meta_version' = meta_version + 1
        /\ meta_fragments' = c.fragments
        /\ meta_status' = STATUS_OPEN
        /\ UNCHANGED << bookie_vars, messages, meta_term, meta_last_entry >>

(***************************************************************************)
(* Initial and Next state                                                  *)
(***************************************************************************)

Init ==
    /\ messages = [msg \in {} |-> 0]
    /\ meta_term = 0
    /\ meta_status = Nil
    /\ meta_last_entry = 0
    /\ meta_fragments = <<>>
    /\ meta_version = 0
    /\ b_term = [b \in Bookies |-> 0]
    /\ b_entries = [b \in Bookies |-> {}]
    /\ b_lac = [b \in Bookies |-> 0]
    /\ b_lafr = [b \in Bookies |-> 0]
    /\ clients = [cid \in Clients |-> InitClient(cid)]

Next ==
    \* Bookies
    \/ BookieRejectsRequest
    \/ BookieSendsAddConfirmedResponse
    \/ BookieSendsFencingReadLafrResponse
    \/ BookieSendsReadResponse
    \* Clients
    \/ ClientWithdraws
    \/ \E cid \in Clients :
        \/ ClientCreatesLedger(cid)
        \/ ClientSendsAddEntryRequests(cid)
        \/ ClientReceivesAddConfirmedResponse(cid)
        \/ ClientChangesEnsemble(cid)
        \/ ClientResendsPendingAddOp(cid)
        \/ ClientClosesLedgerSuccess(cid)
        \/ ClientClosesLedgerFail(cid)
        \/ ClientStartsNewTerm(cid)
        \/ ClientReceivesFencingReadLafrResponse(cid)
        \/ ClientSendsRecoveryReadRequests(cid)
        \/ ClientReceivesRecoveryReadResponse(cid)
        \/ ClientWritesBackEntry(cid)
        \/ RecoveryClientReceivesAddConfirmedResponse(cid)
        \/ RecoveryClientChangesEnsemble(cid)
        \/ RecoveryClientSendsPendingAddOp(cid)
        \/ ClientChangesTermToOpen(cid)


(***************************************************************************
Invariant: TypeOK                                                       

Check that the variables hold the correct data types                    
****************************************************************************)

TypeOK ==
    /\ meta_status \in { Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED }
    /\ meta_last_entry \in Nat
    /\ meta_version \in Nat
    /\ b_term \in [Bookies -> Nat]
    /\ b_entries \in [Bookies -> SUBSET Entry]
    /\ b_lac \in [Bookies -> Nat]
\*    /\ clients \in [Clients -> ClientState]

(***************************************************************************
Invariant: No Divergence Between Clients And MetaData                   

This invariant is violated if, once a ledger is closed, any client has  
an entry acknowledged (by AQ bookies) that has a higher entry id than   
the endpoint of the ledger as stored in the metadata store.             
This divergence is known as Ledger Truncation and it data loss.                                       
****************************************************************************)

NoDivergenceBetweenClientAndMetaData ==
    IF meta_status # STATUS_CLOSED
    THEN TRUE
    ELSE \A c \in DOMAIN clients :
            \/ clients[c].status = Nil
            \/ /\ clients[c].status # Nil
               /\ \A id \in 1..clients[c].lac : id <= meta_last_entry

(***************************************************************************
Invariant: All confirmed entries are readable                           

This invariant is violated if, once an entry has been acknowledged, it  
is no longer readable from its ensemble.
****************************************************************************)
AllAckedEntriesAreReadable ==
    \A cid \in Clients :
        IF /\ clients[cid].status \in {STATUS_OPEN, STATUS_CLOSED}
           /\ clients[cid].lac > 0
        THEN \A entry_id \in 1..clients[cid].lac :
                \E b \in FragmentOfEntryId(entry_id, meta_fragments).ensemble : 
                    \E entry \in b_entries[b] :
                        entry.id = entry_id
        ELSE TRUE

(***************************************************************************
Invariant: No dirty reads                        

This invariant is violated if a client were allowed to read an entry
that was not committed. To do that a client would need to read past the LAC.
That is simple to prevent, the bookie must simply reject any regular
reads past this point. This spec does not model regular reads.

This invariant instead goes further by checking that the LAC of each bookie
has indeed reached Ack Quorum and therefore committed.
****************************************************************************)
NoDirtyReads ==
    \A b \in Bookies :
        \/ b_lac[b] = 0 \* we only care about bookies with LAC > 0
        \/ /\ b_lac[b] > 0
           /\ LET ensemble == FragmentOfEntryId(b_lac[b], meta_fragments).ensemble
              IN
                \/ b \notin ensemble \* we only care about bookies in the ensemble
                \/ /\ b \in ensemble
                   /\ Quantify(ensemble, 
                        LAMBDA bk : \E e \in b_entries[bk] : e.id = b_lac[b]) >= AckQuorum         

(***************************************************************************
Invariant: TailFragmentsReachWriteQuorum
Invariant: AllEntriesOfClosedLedgerReachedWriteQuorum             

This invariant is violated if, once a ledger is closed, there exists    
any entry that is less than Ack Quorum replicated.                      
NOTE: This invariant only applies if we don't model data loss in bookies.
****************************************************************************)
EntryIdReachesWriteQuorum(ensemble, entry_id) ==
    Quantify(ensemble, LAMBDA b : \E e \in b_entries[b] : e.id = entry_id) >= WriteQuorum

TailFragmentsReachWriteQuorum ==
    IF Cardinality(DOMAIN meta_fragments) = 1
    THEN TRUE
    ELSE \A f \in DOMAIN meta_fragments :
        IF meta_fragments[f] = Last(meta_fragments)
        THEN TRUE
        ELSE \A entry_id \in meta_fragments[f].first_entry_id..meta_fragments[f+1].first_entry_id - 1 :
            EntryIdReachesWriteQuorum(meta_fragments[f].ensemble, entry_id)

AllEntriesOfClosedLedgerReachedWriteQuorum ==
    IF meta_status = STATUS_CLOSED
    THEN \A entry_id \in 1..meta_last_entry :
            LET fragment == FragmentOfEntryId(entry_id, meta_fragments)
            IN EntryIdReachesWriteQuorum(fragment.ensemble, entry_id)
    ELSE TRUE

(***************************************************************************
Invariant: Read order matches write order                                                        
                                                                         
Ordering is set by the client that writes the data as it sets the entry ids. 
How data is stored is an implementation detail and not relevant to us. 
The point of this invariant is that if a client were to read the entries back,
would they read the data in the same order?
This is achieved by ensuring that the entry id matches the entry body. In this
spec the original client writes to the ledger with entry bodies that are
monotonically increasing like the entry id does.
***************************************************************************)
NoOutOfOrderEntries ==
    \A b \in Bookies :
        \A entry \in b_entries[b] :
            entry.id = entry.data
           
(************************************************************
Spec and Liveness                                        
Liveness: Eventually, the spec is closed. There are no histories
          where a ledger gets stuck.                 
************************************************************)

LedgerIsClosed ==
    /\ meta_status = STATUS_CLOSED
    /\ \E c \in clients : c.status = STATUS_CLOSED

Liveness ==
    /\ WF_vars(Next)
    /\ []<>LedgerIsClosed

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sat Dec 11 15:33:49 CET 2021 by GUNMETAL
\* Last modified Thu Apr 29 17:55:12 CEST 2021 by jvanlightly