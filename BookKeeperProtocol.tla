------------------------- MODULE BookKeeperProtocol -------------------------
EXTENDS MessagePassing, Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
Represents master branch (aspirational). Models only the lifetime of a single ledger.
See the readme for more information.
*)

\* Input parameters
CONSTANTS Bookies,                      \* The bookies available e.g. { B1, B2, B3, B4 }
          Clients,                      \* The clients e.g. {c1, c2}
          WriteQuorum,                  \* The replication factor under normal circumstances
          AckQuorum,                    \* The number of bookies that must confirm an entry for the
                                        \* client to acknowledge to its own client, also the minimum
                                        \* replication factor (can occur in scenarios such as ensemble change or ledger closes)
          SendLimit                     \* The data items to send. Limited to a very small number of data items
                                        \* in order to keep the state space small. E.g 1 or 2

\* Model values
CONSTANTS Nil,
          NoSuchEntry,
          Unknown,
          OK,
          NeedMoreResponses,
          STATUS_OPEN,
          STATUS_IN_RECOVERY,
          STATUS_CLOSED,
          CLIENT_WITHDRAWN,
          RECOVERY_ABORTED

\* Ledger state in the metadata store
VARIABLES meta_status,              \* the ledger status
          meta_fragments,           \* ledger fragments
          meta_last_entry,          \* the endpoint of the ledger (set on closing)
          meta_version              \* ledger metadata version

\* Bookie state (each is a function whose domain is the set of bookies) pertaining to this single ledger
VARIABLES b_entries,                \* the entries stored in each bookie
          b_fenced,                 \* the fenced status of each bookie (TRUE/FALSE)
          b_lac                     \* the last add confirmed of each bookie

\* the state of the clients
VARIABLES clients                   \* the set of BookKeeper clients

ASSUME SendLimit \in Nat
ASSUME SendLimit > 0
ASSUME WriteQuorum \in Nat
ASSUME WriteQuorum > 0
ASSUME AckQuorum \in Nat
ASSUME AckQuorum > 0
ASSUME WriteQuorum >= AckQuorum

bookie_vars == << b_fenced, b_entries, b_lac >>
meta_vars == << meta_status, meta_fragments, meta_last_entry, meta_version >>
vars == << bookie_vars, clients, meta_vars, messages >>

(***************************************************************************)
(* Recovery Phases                                                         *)
(* In order to reduce the state space, recovery reads and writes are split *)
(* into a read phase and a write phase.                                    *)
(* The implementation works with reads and writes concurrently but this    *)
(* does not affect correctness.                                            *)
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
     fragments: [Nat -> Fragment],              \* The fragments of the ledger known by the client
     curr_fragment: Fragment \union {Nil},      \* The current fragment known by a client
     pending_add_ops: SUBSET PendingAddOp,      \* The pending add operations of a client
     lap: Nat,                                  \* The Last Add Pushed of a client
     lac: Nat,                                  \* The Last Add Confirmed of a client
     confirmed: [EntryIds -> SUBSET Bookies],   \* The bookies that have confirmed each entry id
     fenced: SUBSET Bookies,                    \* The bookies that have confirmed they are fenced to this client
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
     curr_fragment          |-> Nil,
     fragments              |-> <<>>,
     pending_add_ops        |-> {},
     lap                    |-> 0,
     lac                    |-> 0,
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
        
(***************************************************************************)
(* QuorumCoverage                                                          *)
(*                                                                         *)
(* Quorum coverage is a quorum that is required in two places in the       *)
(* protocol:                                                               *)
(* - LAC fencing requests must have been confirmed such that there exists  *)
(*   no ack quorum of bookies in the current ledger ensemble that remain   *)
(*   unfenced.                                                             *)
(* - An entry is only unrecoverable when there is no ack quorum of bookies *)
(*   of the entry ensemble that have or could confirm they have the entry. *)
(*                                                                         *)
(* This can be expressed in different ways:                                *)
(* - There exists no ack quorum of bookies within the cohort that don't    *)
(*   satisfy the property.                                                 *)
(* - In every ack quorum of bookies of the cohort, at least one bookie     *)
(*   must satisfy the property.                                            *)           
(*                                                                         *)
(* It can also simply be distilled down to (Write Quorum - AckQuorum) + 1  *)
(* bookies must satisfy the property.                                      *)
(* Note that this spec does not model Ensemble size /= Write Quorum so the *)
(* cohort size is always Write Quorum.                                     *)
(*                                                                         *)
(***************************************************************************)

HasQuorumCoverage(s) ==
    Cardinality(s) >= ((WriteQuorum - AckQuorum) + 1)
    
(***************************************************************************)
(* ACTION: Create ledger                                                   *)
(*                                                                         *)
(* A ledger is created with an ensemble that is selected                   *)
(* non-deterministically.                                                  *)
(***************************************************************************)

ClientCreatesLedger(cid) ==
    /\ meta_status = Nil
    /\ clients[cid].meta_version = Nil
    /\ LET fragment == [id |-> 1, ensemble |-> SelectEnsemble({},{}), first_entry_id |-> 1]
       IN
        /\ clients' = [clients EXCEPT ![cid] = 
                                [@ EXCEPT !.status = STATUS_OPEN,
                                          !.meta_version = 1,
                                          !.fragments = Append(meta_fragments, fragment),
                                          !.curr_fragment = fragment]]
        /\ meta_status' = STATUS_OPEN
        /\ meta_version' = 1
        /\ meta_fragments' = Append(meta_fragments, fragment)
    /\ UNCHANGED << bookie_vars, meta_last_entry, messages >>

(***************************************************************************)
(* ACTION: Send Add Entry Requests                                         *)
(*                                                                         *)
(* The client sends an AddEntryRequestMessage to each bookie of the        *)
(* current fragment ensemble. The data sent is simply an integer that      *)
(* increases by one on each send, forming a sequence (1,2,3 etc).          *)
(***************************************************************************)

GetAddEntryRequests(c, entry, ensemble, recovery) ==
    { [type     |-> AddEntryRequestMessage,
       bookie   |-> b,
       cid      |-> c.id,
       entry    |-> entry,
       lac      |-> c.lac,
       recovery |-> recovery] : b \in ensemble }

SendAddEntryRequests(c, entry) ==
    /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                  entry,
                                                  c.curr_fragment.ensemble,
                                                  FALSE))
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
        /\ LET entry_data == c.lap + 1
           IN
            /\ entry_data <= SendLimit
            /\ SendAddEntryRequests(c, [id   |-> entry_data, data |-> entry_data])
        /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: A bookie receives an AddEntryRequestMessage, Sends a confirm.   *)
(*                                                                         *)
(* A bookie receives a AddEntryRequestMessage, the ledger is not fenced so *)
(* it adds the entry and responds with a success response.                 *)
(***************************************************************************)

GetAddEntryResponse(add_entry_msg, success) ==
    [type     |-> AddEntryResponseMessage,
     bookie   |-> add_entry_msg.bookie,
     cid      |-> add_entry_msg.cid,
     entry    |-> add_entry_msg.entry,
     recovery |-> add_entry_msg.recovery,
     success  |-> success]

BookieSendsAddConfirmedResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ IsEarliestMsg(msg)
        /\ \/ b_fenced[msg.bookie] = FALSE
           \/ msg.recovery = TRUE
        /\ b_entries' = [b_entries EXCEPT ![msg.bookie] = @ \union {msg.entry}]
        /\ b_lac' = [b_lac EXCEPT ![msg.bookie] = msg.lac]
        /\ ProcessedOneAndSendAnother(msg, GetAddEntryResponse(msg, TRUE))
        /\ UNCHANGED << b_fenced, clients, meta_vars >>

(***************************************************************************)
(* ACTION: A bookie receives an AddEntryRequestMessage, Sends a fenced     *)
(*         response.                                                       *)
(*                                                                         *)
(* A bookie receives a AddEntryRequestMessage, but the ledger is fenced so *)
(* it responds with a fenced response.                                     *)
(***************************************************************************)

BookieSendsAddFencedResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ msg.recovery = FALSE
        /\ b_fenced[msg.bookie] = TRUE
        /\ IsEarliestMsg(msg)
        /\ ProcessedOneAndSendAnother(msg, GetAddEntryResponse(msg, FALSE))
        /\ UNCHANGED << bookie_vars, clients, meta_vars >>

(***************************************************************************)
(* ACTION: A client receive a success AddEntryResponseMessage              *)
(*                                                                         *)
(* A client receives a success AddEntryResponseMessage and adds the bookie *)
(* to the list of bookies that have acknowledged the entry.                *)
(* It may also:                                                            *)
(* - advance the LAC.                                                      *)
(* - remove pending add ops that are equal to or lower than the new LAC    *)
(*                                                                         *)
(* The LAC is only advanced to the entry of this confirm if the entry has  *)
(* reached Ack Quorum and all prior entries are also ack quorum replicated.*)
(***************************************************************************)

AddToConfirmed(c, entry_id, bookie) ==
    [c.confirmed EXCEPT ![entry_id] = @ \union {bookie}]

\* Only remove if it has reached the Ack Quorum and <= LAC
MayBeRemoveFromPending(c, confirmed, lac) ==
    { op \in c.pending_add_ops :
        \/ Cardinality(confirmed[op.entry.id]) < AckQuorum
        \/ op.entry.id > lac
    }

MaxContiguousConfirmedEntry(confirmed) ==
    IF \E id \in DOMAIN confirmed : \A id1 \in 1..id :
                                        Cardinality(confirmed[id1]) >= AckQuorum
    THEN Max({id \in DOMAIN confirmed :
                \A id1 \in 1..id :
                    Cardinality(confirmed[id1]) >= AckQuorum
             })
    ELSE 0

ReceiveAddConfirmedResponse(c, is_recovery) ==
    \E msg \in DOMAIN messages :
        /\ msg.cid = c.id
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = is_recovery
        /\ msg.success = TRUE
        /\ msg.bookie \in c.curr_fragment.ensemble
        /\ LET confirmed == AddToConfirmed(c, msg.entry.id, msg.bookie)
           IN LET lac == MaxContiguousConfirmedEntry(confirmed)
              IN
                clients' = [clients EXCEPT ![c.id] = 
                                        [c EXCEPT !.confirmed = confirmed,
                                                  !.lac = IF lac > @ THEN lac ELSE @,
                                                  !.pending_add_ops = MayBeRemoveFromPending(c, confirmed, lac)]]
        /\ MessageProcessed(msg)


ClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ ReceiveAddConfirmedResponse(clients[cid], FALSE)
    /\ UNCHANGED << bookie_vars, meta_vars >>

RecoveryClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ReceiveAddConfirmedResponse(clients[cid], TRUE)
    /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: A client receives a fenced AddEntryResponseMessage              *)
(*                                                                         *)
(* The client receives a fenced AddEntryResponseMessage which means ledger *)
(* recovery has been initiated and the ledger has been fenced on that      *)
(* bookie.                                                                 *)
(* Therefore the client ceases further interactions with this ledger.      *)
(***************************************************************************)

ClientReceivesAddFencedResponse(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ \E msg \in DOMAIN messages :
        /\ msg.cid = cid
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = FALSE
        /\ msg.success = FALSE
        /\ msg.bookie \in clients[cid].curr_fragment.ensemble
        /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN]]
        /\ MessageProcessed(msg)
        /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: A client performs an ensemble change.                           *)
(*                                                                         *)
(* A write to a bookie has failed (in this spec due to timeout).           *)
(* The client:                                                             *)
(*  - opens a new fragment with a new ensemble, with its first entry id    *)
(*    being LAC + 1.                                                       *)
(*  - removes the failed bookie from the confirmed set of any non-committed*)
(*    entries. For entries that have Ack Quorum but are ahead of the LAC,  *)
(*    and therefore not committed, this can reduce them back down to       *)
(*    below AckQuorum.                                                     *)
(*                                                                         *)
(* NOTE1: we don't need to model the client closing the ledger at this     *)
(*       point due no other ensembles being available because this spec    *)
(*       allows the client to close the ledger at any time anyway.         *)
(*                                                                         *)
(* NOTE2: Before triggering another ensemble change, we ensure that all    *)
(*        pending add ops that need to be sent to bookies due to a prior   *)
(*        ensemble change, do get sent first.                              *)
(***************************************************************************)

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
    /\ \E bookie \in c.curr_fragment.ensemble :
        /\ WriteTimeoutForBookie(messages, c.id, bookie, recovery)
        /\ EnsembleAvailable(c.curr_fragment.ensemble \ {bookie}, {bookie})
        /\ ValidNextFragment(c.lac + 1)
        /\ LET new_ensemble   == SelectEnsemble(c.curr_fragment.ensemble \ {bookie}, {bookie})
               first_entry_id == c.lac + 1
           IN LET updated_fragments == UpdatedFragments(c, first_entry_id, new_ensemble)
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
                                                                   THEN c.confirmed[id] \ {bookie}
                                                                   ELSE c.confirmed[id]],
                                              !.fragments     = updated_fragments,
                                              !.curr_fragment = Last(updated_fragments)]]
                /\ ClearWriteTimeout(c.id, bookie, recovery)

ClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ ChangeEnsemble(clients[cid], FALSE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_last_entry >>

RecoveryClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ meta_status = STATUS_IN_RECOVERY
    /\ ChangeEnsemble(clients[cid], TRUE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_last_entry >>

(***************************************************************************)
(* ACTION: Client resends a Pending Add Op                                 *)
(*                                                                         *)
(* A pending add op needs to be sent to one or more bookies of a           *)
(* new ensemble due to a previous bookie write failure.                    *)
(* We resend a pending add op when it has a different fragment id          *) 
(* or different ensemble to the current fragment (basically the op was not *)
(* updated yet with the ensemble change.                                   *)  
(* The ensemble change may have been a replacement rather than appended    *)
(* so the id may be the same but the ensemble different, hence checking    *)
(* both.                                                                   *)
(***************************************************************************)

\* update the pending add op ensemble
SetNewEnsemble(c, pending_op) ==
    {
        IF op = pending_op
        THEN [entry       |-> op.entry,
              fragment_id |-> c.curr_fragment.id,
              ensemble    |-> c.curr_fragment.ensemble]
        ELSE op : op \in c.pending_add_ops
    }

\* send the add to any bookies in the new ensemble that are not in the original
\* then update the op with the new ensemble.
SendPendingAddOp(c, is_recovery) ==
    /\ \E op \in c.pending_add_ops :
        /\ \/ op.fragment_id # c.curr_fragment.id
           \/ op.ensemble # c.curr_fragment.ensemble
        /\ ~\E op2 \in c.pending_add_ops :
            /\ op2.fragment_id = op.fragment_id
            /\ op2.ensemble = op.ensemble
            /\ op2.entry.id < op.entry.id
        /\ LET new_bookies == c.curr_fragment.ensemble \ op.ensemble
           IN
              /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                            op.entry,
                                                            new_bookies,
                                                            is_recovery))
              /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.pending_add_ops = SetNewEnsemble(c, op)]]

ClientSendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ SendPendingAddOp(clients[cid], FALSE)
    /\ UNCHANGED << bookie_vars, meta_vars >>

RecoveryClientSendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ SendPendingAddOp(clients[cid], TRUE)
    /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: A client closes its own ledger.                                 *)
(*                                                                         *)
(* The client decides to close its ledger. The metadata store still        *)
(* has the ledger as open so the close succeeds.                           *)
(* A close can happen at any time.                                         *)
(***************************************************************************)

ClientClosesLedgerSuccess(cid) ==
    /\ clients[cid].meta_version = meta_version
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ clients' = [clients EXCEPT ![cid] = 
                        [@ EXCEPT !.meta_version = @ + 1,
                                  !.status = STATUS_CLOSED]]
    /\ meta_status' = STATUS_CLOSED
    /\ meta_last_entry' = clients[cid].lac
    /\ meta_version' = meta_version + 1
    /\ UNCHANGED << bookie_vars, meta_fragments, messages >>

(***************************************************************************)
(* ACTION: A client fails to close its own ledger.                         *)
(*                                                                         *)
(* The client decides to close its ledger. The metadata store has the      *)
(* ledger as not open so the close fails and the client ceases further     *)
(* interactions with this ledger (we do not model a stalled recovery).     *)
(***************************************************************************)

\* DISABLING THIS REDUCES THE STATE SPACE, CAN UNCOMMENT TO INCLUDE IT

ClientClosesLedgerFail(cid) ==
    /\ clients[cid].meta_version # meta_version
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status # STATUS_OPEN
    /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN,
                                                     !.meta_version = Nil]]
    /\ UNCHANGED << bookie_vars, meta_vars, messages >>

(***************************************************************************)
(* ACTION: A client start ledger recovery.                                 *)
(*                                                                         *)
(* A recovery client decides to start the recovery process for the ledger. *)
(* Changes the meta status to IN_RECOVERY and sends a fencing read LAC     *)
(* request to each bookie in the current ensemble.                         *)
(*                                                                         *)
(***************************************************************************)

GetFencedReadLacRequests(c, ensemble) ==
    { [type   |-> FenceRequestMessage,
       bookie |-> bookie,
       cid    |-> c.id] : bookie \in ensemble }

ClientStartsRecovery(cid) ==
    /\ clients[cid].status = Nil
    /\ meta_status \in {STATUS_OPEN, STATUS_IN_RECOVERY}
    /\ meta_status' = STATUS_IN_RECOVERY
    /\ meta_version' = meta_version + 1
    /\ clients' = [clients EXCEPT ![cid] =
                            [@ EXCEPT !.status            = STATUS_IN_RECOVERY,
                                      !.meta_version      = meta_version + 1,
                                      !.recovery_phase    = FencingPhase,
                                      !.fragments         = meta_fragments,
                                      !.curr_fragment     = Last(meta_fragments),
                                      !.recovery_ensemble = Last(meta_fragments).ensemble]]
    /\ SendMessagesToEnsemble(GetFencedReadLacRequests(clients[cid], Last(meta_fragments).ensemble))
    /\ UNCHANGED << bookie_vars, meta_fragments, meta_last_entry >>

(***************************************************************************)
(* ACTION: A bookie receives a fencing LAC request, send a response.       *)
(*                                                                         *)
(* A bookie receives a fencing read LAC request and sends back a success   *)
(* response with its LAC.                                                  *)
(***************************************************************************)

GetFencingReadLacResponseMessage(msg) ==
    [type   |-> FenceResponseMessage,
     bookie |-> msg.bookie,
     cid    |-> msg.cid,
     lac    |-> b_lac[msg.bookie]]

BookieSendsFencingReadLacResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, FenceRequestMessage)
        /\ b_fenced' = [b_fenced EXCEPT ![msg.bookie] = TRUE]
        /\ ProcessedOneAndSendAnother(msg, GetFencingReadLacResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, clients, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a fence response                                        *)
(*                                                                         *)
(* A recovery client receives a success FenceResponseMessage               *)
(* and takes note of the bookie that confirmed its fenced status and if    *)
(* its LAC is highest, stores it.                                          *)
(* Once the read phase has started any late arriving LAC reads are ignored.*)
(***************************************************************************)

ClientReceivesFencingReadLacResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.recovery_phase = FencingPhase \* we can ignore any late responses after 
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, FenceResponseMessage)
            /\ LET lac == IF msg.lac > c.curr_fragment.first_entry_id - 1
                          THEN msg.lac
                          ELSE c.curr_fragment.first_entry_id - 1
               IN
                /\ clients' = [clients EXCEPT ![cid] = 
                                    [@ EXCEPT !.fenced = @ \union {msg.bookie},
                                              !.lac = IF lac > @ THEN lac ELSE @,
                                              !.lap = IF lac > @ THEN lac ELSE @]]
                /\ MessageProcessed(msg)
                /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: Recovery client sends a recovery read request to each bookie.   *)
(*                                                                         *)
(* The recovery client sends a ReadRequestMessage to each bookie of the    *)
(* recovery read ensemble once every ack quorum has at least one fenced    *)
(* bookie. Recovery reads set the fencing flag.                            *)
(*                                                                         *)
(* It is important to remember that recovery reads get sent to the         *)
(* ensemble of the last fragment at the time recovery started - called the *)
(* recovery read ensemble in this spec. If reads get sent to the current   *)
(* ensemble then ensemble changes resulting from recovery writes can cause *)
(* reads to be sent to bookies that do not have the entries and the result *)
(* would be ledger truncation.                                             *)
(*                                                                         *)
(* NOTE1: Remember that entry ids start at 1 in this spec as TLA+ is base 1*)
(***************************************************************************)

GetRecoveryReadRequests(c, entry_id, ensemble) ==
    { [type     |-> ReadRequestMessage,
       bookie   |-> b,
       cid      |-> c.id,
       entry_id |-> entry_id,
       fence    |-> TRUE] : b \in ensemble }

ClientSendsRecoveryReadRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ \/ /\ c.recovery_phase = ReadWritePhase
              /\ c.last_recoverable_entry = Nil
              /\ c.curr_read_entry = Nil
           \/ /\ c.recovery_phase = FencingPhase
              /\ HasQuorumCoverage(c.fenced) 
        /\ LET next_entry_id == c.lap+1
           IN
            /\ clients' = [clients EXCEPT ![c.id] = [c EXCEPT !.recovery_phase  = ReadWritePhase,
                                                              !.curr_read_entry = next_entry_id,
                                                              !.fenced          = {}]] \* fenced no longer needed to reset
            /\ SendMessagesToEnsemble(GetRecoveryReadRequests(c, next_entry_id, c.recovery_ensemble))
            /\ UNCHANGED << bookie_vars, meta_vars >>

(***************************************************************************)
(* ACTION: A bookie receive a read request, sends a response.              *)
(*                                                                         *)
(* A bookie receives a ReadRequestMessage and sends back a success         *)
(* response if it has the entry and a non-success if it doesn't.           *)
(***************************************************************************)

GetReadResponseMessage(msg) ==
    [type     |-> ReadResponseMessage,
     bookie   |-> msg.bookie,
     cid      |-> msg.cid,
     entry    |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN CHOOSE entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  ELSE [id |-> msg.entry_id, data |-> Nil],
     fence    |-> msg.fence,
     code     |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN OK
                  ELSE NoSuchEntry]

BookieSendsReadResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadRequestMessage)
        /\ IF msg.fence = TRUE \* only recovery reads modelled which are always fenced
           THEN b_fenced' = [b_fenced EXCEPT ![msg.bookie] = TRUE]
           ELSE UNCHANGED << b_fenced >>
        /\ ProcessedOneAndSendAnother(msg, GetReadResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, clients, meta_vars >>

(***************************************************************************)
(* ACTION: Client receives a read response.                                *)
(*                                                                         *)
(* On receiving each response, the recovery client must decide whether     *)
(* the entry is recoverable, non-recoverable or needs more responses to    *)
(* decide. In order to balance performance with safety, the client is      *)
(* generous with positive results (only requires one positive read to      *)
(* treat an entry as recoverable) but strict on negative results (requires *)
(* quorum coverage of NoSuchEntry responses to treat an entry as           *)
(* unrecoverable).                                                         *)
(*                                                                         *)
(* If the entry is recoverable then the entry is adding to the list of     *)
(* pending add ops that must be sent in the Write Phase. The next action   *)
(* will be to send recovery reads of the next entry.                       *)
(*                                                                         *)
(* If the entry is unrecoverable, then the read phase is finished.         *)
(*                                                                         *)
(* If all responses have been received and still neither the positive      *)
(* threshold of 1 or the negative threshold of quorum coverage (WQ-AQ)+1   *)
(* has been reached, the final result of the read is Unknown, and the      *)
(* recovery is aborted.                                 *)
(***************************************************************************)

ReadStatus(c, responses) ==
    IF \E msg \in responses : msg.code = OK 
    THEN OK \* generous on positive results
    ELSE \* strict on negative
         IF HasQuorumCoverage({msg \in responses : msg.code = NoSuchEntry })
         THEN NoSuchEntry
         ELSE \* all responses in and neither positive nor negative threshold reached
              IF Cardinality(responses) 
                + ReadTimeoutCount(c.id, c.recovery_ensemble, TRUE) = WriteQuorum
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
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
      
ReadNegative(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.curr_read_entry        = Nil, \* reset to reduce state space
                              !.read_responses         = {},  \* reset to reduce state space
                              !.recovery_ensemble      = {},  \* reset to reduce state space
                              !.last_recoverable_entry = msg.entry.id - 1]]
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
    
ReadUnknown(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.status = RECOVERY_ABORTED,
                              !.curr_read_entry   = Nil, \* reset to reduce state space
                              !.read_responses    = {},  \* reset to reduce state space
                              !.recovery_ensemble = {}]] \* reset to reduce state space
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
    
NotEnoughReadResponses(c, msg, responses) ==
    clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.read_responses = responses]]    
    
ClientReceivesRecoveryReadResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.status = STATUS_IN_RECOVERY
       /\ c.recovery_phase = ReadWritePhase
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
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

(***************************************************************************)
(* ACTION: Client writes back a entry that was successfully read.          *)
(*                                                                         *)
(* Recovery writes follow the same logic as replication writes, in that    *)
(* they can involve the creation of new fragments. Also note that all      *)
(* entries are written to the current fragment, not necessarily the        *)
(* fragment they were read from (recovery_ensemble).                       *)
(***************************************************************************)

NotSentWrite(c, op) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = AddEntryRequestMessage
        /\ msg.cid = c.id
        /\ msg.recovery = TRUE
        /\ msg.entry = op.entry

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
                                                          c.curr_fragment.ensemble,
                                                          TRUE))
        /\ UNCHANGED << bookie_vars, clients, meta_vars >>

(***************************************************************************)
(* ACTION: Recovery client closes the ledger.                              *)
(*                                                                         *)
(* Once all the entries that were read during recovery have been           *)
(* successfully written back recovery is complete. Update metadata:        *)
(* - status to CLOSED                                                      *)
(* - Last Entry id to the highest recovered entry id                       *)
(* - the fragments (which may have changed due to ensemble changes during  *)
(*   recovery)                                                             *)
(***************************************************************************)

RecoveryClientClosesLedger(cid) ==
    LET c == clients[cid]
    IN
        /\ meta_version = c.meta_version
        /\ meta_status = STATUS_IN_RECOVERY
        /\ c.status = STATUS_IN_RECOVERY
        /\ c.recovery_phase = ReadWritePhase
        /\ c.last_recoverable_entry # Nil
        /\ Cardinality(c.pending_add_ops) = 0
        /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.status = STATUS_CLOSED,
                                          !.meta_version = @ + 1]]
        /\ meta_version' = meta_version + 1
        /\ meta_fragments' = c.fragments
        /\ meta_status' = STATUS_CLOSED
        /\ meta_last_entry' = c.last_recoverable_entry
        /\ UNCHANGED << bookie_vars, meta_fragments, messages >>

(***************************************************************************)
(* Initial and Next state                                                  *)
(***************************************************************************)

Init ==
    /\ messages = [msg \in {} |-> 0]
    /\ meta_status = Nil
    /\ meta_last_entry = 0
    /\ meta_fragments = <<>>
    /\ meta_version = 0
    /\ b_fenced = [b \in Bookies |-> FALSE]
    /\ b_entries = [b \in Bookies |-> {}]
    /\ b_lac = [b \in Bookies |-> 0]
    /\ clients = [cid \in Clients |-> InitClient(cid)]

Next ==
    \* Bookies
    \/ BookieSendsAddConfirmedResponse
    \/ BookieSendsAddFencedResponse
    \/ BookieSendsFencingReadLacResponse
    \/ BookieSendsReadResponse
    \/ \E cid \in Clients :
        \* original client
        \/ ClientCreatesLedger(cid)
        \/ ClientSendsAddEntryRequests(cid)
        \/ ClientReceivesAddConfirmedResponse(cid)
        \/ ClientReceivesAddFencedResponse(cid)
        \/ ClientChangesEnsemble(cid)
        \/ ClientSendsPendingAddOp(cid)
        \/ ClientClosesLedgerSuccess(cid)
        \/ ClientClosesLedgerFail(cid)
        \* recovery clients
        \/ ClientStartsRecovery(cid)
        \/ ClientReceivesFencingReadLacResponse(cid)
        \/ ClientSendsRecoveryReadRequests(cid)
        \/ ClientReceivesRecoveryReadResponse(cid)
        \/ ClientWritesBackEntry(cid)
        \/ RecoveryClientReceivesAddConfirmedResponse(cid)
        \/ RecoveryClientChangesEnsemble(cid)
        \/ RecoveryClientSendsPendingAddOp(cid)
        \/ RecoveryClientClosesLedger(cid)


(***************************************************************************)
(* Invariant: TypeOK                                                       *)
(*                                                                         *)
(* Check that the variables hold the correct data types                    *)
(***************************************************************************)

TypeOK ==
    /\ meta_status \in { Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED }
    /\ meta_last_entry \in Nat
    /\ meta_version \in Nat
    /\ b_fenced \in [Bookies -> BOOLEAN]
    /\ b_entries \in [Bookies -> SUBSET Entry]
    /\ b_lac \in [Bookies -> Nat]
\*    /\ clients \in [Clients -> ClientState]

(***************************************************************************)
(* Invariant: No Divergence Between Clients And MetaData                   *)
(*                                                                         *)
(* This invariant is violated if, once a ledger is closed, the writer has  *)
(* an entry acknowledged (by Qa bookies) that has a higher entry id than   *)
(* the endpoint of the ledger as stored in the metadata store.             *)
(* This is divergence and data loss.                                       *)
(***************************************************************************)
NoDivergenceBetweenClientAndMetaData ==
    IF meta_status # STATUS_CLOSED
    THEN TRUE
    ELSE \A c \in DOMAIN clients :
            \/ clients[c].status = Nil
            \/ /\ clients[c].status # Nil
               /\ \A id \in 1..clients[c].lac : id <= meta_last_entry

(***************************************************************************)
(* Invariant: All committed entries reach Ack Quorum                       *)
(*                                                                         *)
(* This invariant is violated if, once a ledger is closed, there exists    *)
(* any entry that is less than Ack Quorum replicated.                      *)
(* NOTE: This invariant should only be checked when not including          *)
(*       BookieRestartsEmpty actions                                       *)
(***************************************************************************)
EntryIdReachesAckQuorum(ensemble, entry_id) ==
    Quantify(ensemble, LAMBDA b : \E e \in b_entries[b] : e.id = entry_id) >= AckQuorum
\*    Cardinality({ b \in ensemble : \E e \in b_entries[b] : e.id = entry_id }) >= AckQuorum

AllCommittedEntriesReachAckQuorum ==
    IF meta_status # STATUS_CLOSED
    THEN TRUE
    ELSE IF meta_last_entry > 0
         THEN \A id \in 1..meta_last_entry :
                LET fragment == FragmentOfEntryId(id, meta_fragments)
                IN EntryIdReachesAckQuorum(fragment.ensemble, id)
         ELSE TRUE

(***************************************************************************)
(* Invariant: Entries must be stored in the same order the writer sent     *)
(*            them.                                                        *)
(*                                                                         *)
(* This invariant would be violated if say the recovery process recovered  *)
(* data leaving it out-of-order. The entry data added by w1 is a monotonic *)
(* counter, exactly the same as the entry id. If the entry id does not     *)
(* match the entry data, then we have an ordering violation.               *)
(***************************************************************************)
NoOutOfOrderEntries ==
    \A b \in Bookies :
        \A entry \in b_entries[b] :
            entry.id = entry.data

(************************************************************)
(* Spec and Liveness                                        *)
(* Liveness: Eventually, the spec is closed                 *)
(************************************************************)

LedgerIsClosed ==
    /\ meta_status = STATUS_CLOSED
    /\ \E c \in clients : c.status = STATUS_CLOSED

Liveness ==
    /\ WF_vars(Next)
    /\ []<>LedgerIsClosed

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sat Nov 27 16:55:45 CET 2021 by GUNMETAL
\* Last modified Thu Apr 29 17:55:12 CEST 2021 by jvanlightly