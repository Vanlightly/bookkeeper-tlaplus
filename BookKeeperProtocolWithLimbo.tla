------------------------- MODULE BookKeeperProtocolWithLimbo -------------------------
EXTENDS MessagePassing, Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
Represents proposed changes to make running BookKeeper without the journal safe (Kafka safety equivalent).
See the readme for more information.
*)

\* Input parameters
CONSTANTS Bookies,                        \* The bookies available e.g. { B1, B2, B3, B4 }
          Clients,                        \* The clients e.g. {c1, c2}
          WriteQuorum,                    \* The replication factor under normal circumstances
          AckQuorum,                      \* The number of bookies required to acknowledge an entry for the
                                          \* writer to acknowledge to its own client, also the minimum
                                          \* replication factor (can occur in scenarios such as ensemble change or ledger closes)
          SendLimit,                      \* The data items to send. Limited to a very small number of data items
                                          \* in order to keep the state space small. E.g 2
          AllowCrashWhenLedgerOpen,       \* Allows a crash with data loss to occur when the ledger is open
          AllowCrashWhenLedgerInRecovery, \* Allows a crash with data loss to occur when the ledger is in recovery
          AllowCrashWhenLedgerClosed,     \* Allows a crash with data loss to occur when the ledger is closed
          FenceOnUncleanShutdown,         \* On boot, when an unclean shutdown is detected, fence the ledger
          SetLimboOnUncleanShutdown       \* On boot, when an unclean shutdown is detected, set limbo status on ledger                               

\* Model values
CONSTANTS Nil,
          NoSuchEntry,
          Unknown,
          OK,
          STATUS_OPEN,
          STATUS_IN_RECOVERY,
          STATUS_CLOSED,
          CLIENT_WITHDRAWN

\* Ledger state in the metadata store
VARIABLES meta_status,              \* the ledger status
          meta_fragments,           \* ledger fragments
          meta_last_entry,          \* the endpoint of the ledger
          meta_version              \* ledger metatdata version

\* Bookie state (each is a function whose domain is the set of bookies) pertaining to this single ledger
VARIABLES b_entries,                \* the entries stored in each bookie
          b_fenced,                 \* the fenced status of each bookie (TRUE/FALSE)
          b_lac,                    \* the last add confirmed of each bookie
          b_limbo                   \* the ledger limbo status on each bookie (TRUE/FALSE)

\* the state of the clients
VARIABLES clients                   \* the set of BookKeeper clients

\* how many crashes have occurred (used to limit the number of crashes)
\* (use a view to remove this from state space)
VARIABLES crashes

ASSUME SendLimit \in Nat
ASSUME SendLimit > 0
ASSUME WriteQuorum \in Nat
ASSUME WriteQuorum > 0
ASSUME AckQuorum \in Nat
ASSUME AckQuorum > 0
ASSUME WriteQuorum >= AckQuorum
ASSUME AllowCrashWhenLedgerOpen \in BOOLEAN
ASSUME AllowCrashWhenLedgerInRecovery \in BOOLEAN
ASSUME AllowCrashWhenLedgerClosed \in BOOLEAN
ASSUME FenceOnUncleanShutdown \in BOOLEAN
ASSUME SetLimboOnUncleanShutdown \in BOOLEAN


bookie_vars == << b_fenced, b_entries, b_lac, b_limbo >>
meta_vars == << meta_status, meta_fragments, meta_last_entry, meta_version >>
vars == << bookie_vars, clients, meta_vars, messages, crashes >>

(***************************************************************************)
(* Recovery Phases                                                         *)
(* In order to reduce the state space, w2 goes through recovery in phases. *)
(* The implementation works with reads and writes concurrently but this    *)
(* does not affect correctness.                                            *)
(***************************************************************************)
NotStarted == 0
FencingPhase == 1
ReadPhase == 2
PendingReadResponsePhase == 3
WritePhase == 4

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
     curr_read_entry: Entry \union {Nil},       \* The entry currently being read (during recovery)
     has_entry: SUBSET Bookies,                 \* Which bookies confirmed they have the current entry being read
     no_such_entry: SUBSET Bookies,             \* Which bookies confirmed they do not have the current entry being read
     is_unknown: SUBSET Bookies,                \* Which bookies have responded saying they don't know if they have the current entry being read
     recovery_phase: 0..WritePhase]             \* The recovery phase (an artifical phase for reducing state space)

\* Each client starts empty, no state
InitClient(cid) ==
    [id              |-> cid,
     meta_version    |-> Nil,
     status          |-> Nil,
     curr_fragment   |-> Nil,
     fragments       |-> <<>>,
     pending_add_ops |-> {},
     lap             |-> 0,
     lac             |-> 0,
     confirmed       |-> [id \in EntryIds |-> {}],
     fenced          |-> {},
     curr_read_entry |-> Nil,
     has_entry       |-> {},
     no_such_entry   |-> {},
     is_unknown      |-> {},
     recovery_phase  |-> 0]

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
    /\ UNCHANGED << bookie_vars, meta_last_entry, messages, crashes >>

(***************************************************************************)
(* ACTION: Send Add Entry Requests for a given data item                   *)
(*                                                                         *)
(* The client sends an AddEntryRequestMessage to each bookie of the        *)
(* current fragment ensemble for a data item not yet sent.                 *)
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
    /\ clients[cid].status = STATUS_OPEN
    /\ LET entry_data == clients[cid].lap + 1
       IN
        /\ entry_data <= SendLimit
        /\ SendAddEntryRequests(clients[cid], [id   |-> entry_data, data |-> entry_data])
    /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: A bookie receive an AddEntryRequestMessage, Sends a confirm.    *)
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
        /\ UNCHANGED << b_fenced, b_limbo, clients, meta_vars, crashes >>

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
        /\ UNCHANGED << bookie_vars, clients, meta_vars, crashes >>

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
    /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

RecoveryClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ReceiveAddConfirmedResponse(clients[cid], TRUE)
    /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

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
        /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

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
        /\ WriteTimeoutForBookie(messages, bookie, recovery)
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
                /\ ClearWriteTimeout(bookie, recovery)

ClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ ChangeEnsemble(clients[cid], FALSE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_last_entry, crashes >>

RecoveryClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ meta_status = STATUS_IN_RECOVERY
    /\ ChangeEnsemble(clients[cid], TRUE)
    /\ UNCHANGED <<  bookie_vars, meta_status, meta_last_entry, crashes >>

(***************************************************************************)
(* ACTION: Client resends a Pending Add Op                                 *)
(*                                                                         *)
(* A pending add op needs to be sent to one or more bookies of a           *)
(* new ensemble due to a previous bookie write failure.                    *)
(* We resend a pending add op when it has a different fragment id          *) 
(* or different ensemble the current fragment (basically the op was not    *)
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
    /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

RecoveryClientSendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ SendPendingAddOp(clients[cid], TRUE)
    /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

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
    /\ UNCHANGED << bookie_vars, meta_fragments, messages, crashes >>

(***************************************************************************)
(* ACTION: A client fails to close its own ledger.                         *)
(*                                                                         *)
(* The client decides to close its ledger. The metadata store has the      *)
(* ledger as not open so the close fails and the client ceases further     *)
(* interactions with this ledger (we do not model a stalled recovery).     *)
(***************************************************************************)

ClientClosesLedgerFail(cid) ==
    /\ clients[cid].meta_version # meta_version
    /\ clients[cid].status = STATUS_OPEN
    /\ meta_status # STATUS_OPEN
    /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN,
                                                     !.meta_version = Nil]]
    /\ UNCHANGED << bookie_vars, meta_vars, messages, crashes >>

(***************************************************************************)
(* ACTION: A client start ledger recovery.                                 *)
(*                                                                         *)
(* A second client decides to start the recovery process for the ledger.   *)
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
                            [@ EXCEPT !.status         = STATUS_IN_RECOVERY,
                                      !.meta_version   = meta_version + 1,
                                      !.recovery_phase = FencingPhase,
                                      !.fragments      = meta_fragments,
                                      !.curr_fragment  = Last(meta_fragments)]]
    /\ SendMessagesToEnsemble(GetFencedReadLacRequests(clients[cid], Last(meta_fragments).ensemble))
    /\ UNCHANGED << bookie_vars, meta_fragments, meta_last_entry, crashes >>

(***************************************************************************)
(* ACTION: A bookie receives a fencing LAC request, send a response.       *)
(*                                                                         *)
(* A bookie receives a fencing read LAC request and sends back a success   *)
(* response with its LAC. We only model a single second writer, so this    *)
(* will only happen once per bookie (of current ensemble).                 *)
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
        /\ UNCHANGED << b_entries, b_lac, b_limbo, clients, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: Receive a fence response                                        *)
(*                                                                         *)
(* The second client receives a success FenceResponseMessage               *)
(* and takes note of the bookie that confirmed its fenced status and if    *)
(* its LAC is highest, stores it.                                          *)
(* Once the read phase has started any late arriving LAC reads are ignored.*)
(***************************************************************************)

NotStartedReadPhase ==
    ~\E msg \in DOMAIN messages :
        msg.type = ReadRequestMessage

ClientReceivesFencingReadLacResponse(cid) ==
    LET c == clients[cid]
    IN
        \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, FenceResponseMessage)
            /\ LET lac == IF msg.lac > c.curr_fragment.first_entry_id - 1
                          THEN msg.lac
                          ELSE c.curr_fragment.first_entry_id - 1
               IN
                /\ clients' = [clients EXCEPT ![cid] = 
                                    [@ EXCEPT !.fenced = @ \union {msg.bookie},
                                              !.lac = IF NotStartedReadPhase /\ (c.lac = Nil \/ lac > c.lac)
                                                      THEN lac
                                                      ELSE @,
                                              !.lap = IF NotStartedReadPhase /\ (c.lac = Nil \/ lac > c.lac)
                                                      THEN lac
                                                      ELSE @]]
                /\ MessageProcessed(msg)
                /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: Recovery client send a recovery read request to each bookie.    *)
(*                                                                         *)
(* The second client sends a ReadRequestMessage to each bookie of the      *)
(* current ensemble once every ack quorum has at least one fenced bookie.  *)
(*                                                                         *)
(* NOTE1: Remember that entry ids start at 1 in this spec as TLA+ is base 1*)
(***************************************************************************)

NotSentRead(c, entry_id) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = ReadRequestMessage
        /\ msg.entry_id = entry_id
        /\ msg.cid = c.id

GetRecoveryReadRequests(c, entry_id, ensemble) ==
    { [type     |-> ReadRequestMessage,
       bookie   |-> b,
       cid      |-> c.id,
       entry_id |-> entry_id,
       fence    |-> TRUE] : b \in ensemble }

ClientSendsReadRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ \/ c.recovery_phase = ReadPhase
           \/ /\ c.recovery_phase = FencingPhase
              /\ \A ack_quorum \in { s \in SUBSET c.curr_fragment.ensemble : Cardinality(s) = AckQuorum } :
                    c.fenced \intersect ack_quorum # {}
        /\ LET next_entry_id == c.lap+1
           IN
            /\ NotSentRead(c, next_entry_id)
            /\ clients' = [clients EXCEPT ![c.id] = [c EXCEPT !.recovery_phase = PendingReadResponsePhase]]
            /\ SendMessagesToEnsemble(GetRecoveryReadRequests(c, next_entry_id, 
                                                              FragmentOfEntryId(next_entry_id, c.fragments).ensemble))
            /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

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
                  ELSE Nil,
     fence    |-> msg.fence,
     code     |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN OK
                  ELSE IF b_limbo[msg.bookie] = TRUE
                       THEN Unknown
                       ELSE NoSuchEntry]

BookieSendsReadResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadRequestMessage)
        /\ b_fenced' = [b_fenced EXCEPT ![msg.bookie] = TRUE]
        /\ ProcessedOneAndSendAnother(msg, GetReadResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, b_limbo, clients, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: Client receives a non final read response.                      *)
(*                                                                         *)
(* A recovery client receives either a success ReadResponseMessage         *)
(* or a NoSuchEntry (entry=Nil). This action occurs when there are still   *)
(* more responses pending (including timeouts).                            *)
(***************************************************************************)

ReceivedAllResponses(has_entry, no_such_entry, is_unknown, ensemble) ==
    Cardinality(has_entry) 
    + Cardinality(no_such_entry)
    + Cardinality(is_unknown)  
    + ReadTimeoutCount(ensemble, TRUE) = WriteQuorum

NotEnoughBookies(no_such_entry) ==
    Cardinality(no_such_entry) >= (WriteQuorum - AckQuorum) + 1

EnoughBookies(has_entry) ==
    Cardinality(has_entry) >= AckQuorum

ReadSuccess(read_ensemble, has_entry, no_such_entry, is_unknown) ==
   IF /\ ReceivedAllResponses(has_entry, no_such_entry, is_unknown, read_ensemble)
      /\ EnoughBookies(has_entry)
   THEN TRUE
   ELSE FALSE

ReadIsNoSuchEntry(read_ensemble, has_entry, no_such_entry, is_unknown) ==
    IF /\ ReceivedAllResponses(has_entry, no_such_entry, is_unknown, read_ensemble)
       /\ NotEnoughBookies(no_such_entry)
    THEN TRUE
    ELSE FALSE

ClientReceivesNonFinalRead(cid) ==
    LET c == clients[cid]
    IN
        \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
            /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id, c.fragments).ensemble ELSE {}
                   has_entry     == IF msg.code = OK THEN c.has_entry \union {msg.bookie} ELSE c.has_entry
                   no_such_entry == IF msg.code = NoSuchEntry THEN c.no_such_entry \union {msg.bookie} ELSE c.no_such_entry
                   is_unknown    == IF msg.code = Unknown THEN c.is_unknown \union {msg.bookie} ELSE c.is_unknown
               IN /\ ~ReceivedAllResponses(has_entry, no_such_entry, is_unknown, read_ensemble)
                  /\ clients' = [clients EXCEPT ![c.id] = 
                                        [c EXCEPT !.has_entry       = has_entry,
                                                  !.no_such_entry   = no_such_entry,
                                                  !.is_unknown      = is_unknown,
                                                  !.curr_read_entry = IF msg.entry # Nil THEN msg.entry ELSE @,
                                                  !.fenced          = IF msg.fence = TRUE THEN @ \union {msg.bookie} ELSE @]]
                  /\ MessageProcessed(msg)
            /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: A client recovery read completes successfullly.                 *)
(*                                                                         *)
(* A recovery client receives a recovery read response such that:          *)
(* 1. all responses have either been received or have timed out            *)
(* 2. there are enough bookies to count as a successful read               *)
(* More read requests will subsequently be sent out.                       *)
(***************************************************************************)
ClientCompletesReadSuccessfully(cid) ==
    LET c == clients[cid]
    IN
        \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
            /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id, c.fragments).ensemble ELSE {}
                   has_entry     == IF msg.code = OK THEN c.has_entry \union {msg.bookie} ELSE c.has_entry
                   no_such_entry == IF msg.code = NoSuchEntry THEN c.no_such_entry \union {msg.bookie} ELSE c.no_such_entry
                   is_unknown    == IF msg.code = Unknown THEN c.is_unknown \union {msg.bookie} ELSE c.is_unknown
               IN /\ ReadSuccess(read_ensemble, has_entry, no_such_entry, is_unknown)
                  /\ LET entry_data == IF msg.entry = Nil THEN c.curr_read_entry.data ELSE msg.entry.data
                     IN
                      /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.has_entry       = {}, \* reset for next read
                                          !.no_such_entry   = {}, \* reset for next read
                                          !.is_unknown      = {}, \* reset for next read
                                          !.curr_read_entry = Nil, \* reset for next read
                                          !.fenced          = IF msg.fence = TRUE THEN @ \union {msg.bookie} ELSE @,
                                          !.lap             = @ + 1,
                                          !.pending_add_ops = @ \union {[entry       |-> [id   |-> c.lap + 1,
                                                                                          data |-> entry_data],
                                                                         fragment_id |-> c.curr_fragment.id,
                                                                         ensemble    |-> c.curr_fragment.ensemble]},
                                          !.recovery_phase  = ReadPhase]]
                  /\ ClearReadTimeouts(msg, read_ensemble)
            /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: A recovery read completes with NoSuchEntry/Ledger.              *)
(*                                                                         *)
(* A recovery client receives a read such that:                            *)
(* 1. all responses have either been received or have timed out            *)
(* 2. there are not enough bookies to count as a successful read           *)
(*    NOTE: this is an explicit count of those that confirmed they do not  *)
(*          have the entry. Time outs do not count.                        *)
(* This concludes the read phase. Note that the protocol runs the reads    *)
(* and write concurrently. This spec separates them to reduce the state    *)
(* space.                                                                  *)
(***************************************************************************)

ClientCompletesReadWithNoSuchEntry(cid) ==
    LET c == clients[cid]
    IN
        \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
            /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id, c.fragments).ensemble ELSE {}
                   has_entry     == IF msg.code = OK THEN c.has_entry \union {msg.bookie} ELSE c.has_entry
                   no_such_entry == IF msg.code = NoSuchEntry THEN c.no_such_entry \union {msg.bookie} ELSE c.no_such_entry
                   is_unknown    == IF msg.code = Unknown THEN c.is_unknown \union {msg.bookie} ELSE c.is_unknown
               IN
                  /\ ReadIsNoSuchEntry(read_ensemble, has_entry, no_such_entry, is_unknown)
                  /\ clients' = [clients EXCEPT ![c.id] = 
                                    [c EXCEPT !.has_entry       = {}, \* reset to reduce state space
                                              !.no_such_entry   = {}, \* reset to reduce state space
                                              !.is_unknown      = {}, \* reset to reduce state space
                                              !.curr_read_entry = Nil, \* reset to reduce state space
                                              !.fenced          = IF msg.fence = TRUE
                                                                  THEN @ \union {msg.bookie}
                                                                  ELSE @,
                                              !.recovery_phase  = WritePhase]]
                  /\ ClearReadTimeouts(msg, read_ensemble)
            /\ UNCHANGED << bookie_vars, meta_vars, crashes >>

(***************************************************************************)
(* ACTION: Client writes back a entry that was successfully read.          *)
(*                                                                         *)
(* Recovery writes follow the same logic as replication writes, in that    *)
(* they can involve the creation of new fragments. Also note that all      *)
(* entries are written to the current fragment, not necessarily the        *)
(* fragment they were read from.                                           *)
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
        /\ c.recovery_phase = WritePhase
        /\ \E op \in c.pending_add_ops :
            /\ NotSentWrite(c, op)
            /\ ~\E op2 \in c.pending_add_ops :
                /\ NotSentWrite(c, op2)
                /\ op2.entry.id < op.entry.id
            /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                          op.entry,
                                                          c.curr_fragment.ensemble,
                                                          TRUE))
        /\ UNCHANGED << bookie_vars, clients, meta_vars, crashes >>

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
        /\ c.recovery_phase = WritePhase
        /\ Cardinality(c.pending_add_ops) = 0
        /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.status = STATUS_CLOSED,
                                          !.meta_version = @ + 1]]
        /\ meta_version' = meta_version + 1
        /\ meta_fragments' = c.fragments
        /\ meta_status' = STATUS_CLOSED
        /\ meta_last_entry' = c.lac
        /\ UNCHANGED << bookie_vars, meta_fragments, messages, crashes >>
        
(***************************************************************************)
(* ACTION: Bookie loses all data, starts empty                             *)
(* BY: a bookie                                                            *)
(*                                                                         *)
(* A bookie crashes, comes back up with all data gone                      *)
(* Three variants are availble:                                            *)
(* - outside of a recovery process                                         *)
(* - during fencing                                                        *)
(* - during recovery read phase                                            *)
(*                                                                         *)
(* These variants provide tunable failure scenarios when running TLC.      *)
(* Currently limited to a single crash.                                    *)
(***************************************************************************)

BookieRestartsWithDataLoss ==
    /\ \E b \in Bookies :
        /\ b_entries' = [b_entries EXCEPT ![b] = {}]
        /\ b_lac' = [b_lac EXCEPT ![b] = 0]
        /\ crashes' = crashes + 1
        /\ messages' = [msg \in DOMAIN messages |-> IF /\ msg.type \in {AddEntryRequestMessage, FenceRequestMessage, ReadRequestMessage}
                                                       /\ msg.bookie = b
                                                       /\ messages[msg] = 1
                                                    THEN -1
                                                    ELSE messages[msg]]
        /\ IF SetLimboOnUncleanShutdown
           THEN b_limbo' = [b_limbo EXCEPT ![b] = TRUE]
           ELSE UNCHANGED b_limbo
        /\ IF FenceOnUncleanShutdown
           THEN b_fenced' = [b_fenced EXCEPT ![b] = TRUE]
           ELSE \* the fenced status is lost along with the entries
                b_fenced' = [b_fenced EXCEPT ![b] = FALSE]    
        /\ UNCHANGED << clients, meta_vars >>
        
BookieCrashesWhenLedgerOpen ==
    /\ AllowCrashWhenLedgerOpen
    /\ crashes = 0
    /\ meta_status = STATUS_OPEN
    /\ BookieRestartsWithDataLoss

BookieCrashesWhenLedgerInRecovery ==
    /\ AllowCrashWhenLedgerInRecovery
    /\ crashes = 0
    /\ meta_status = STATUS_IN_RECOVERY
    /\ BookieRestartsWithDataLoss

BookieCrashesWhenLedgerClosed ==
    /\ AllowCrashWhenLedgerClosed
    /\ crashes = 0
    /\ meta_status = STATUS_CLOSED
    /\ BookieRestartsWithDataLoss
        

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
    /\ b_limbo = [b \in Bookies |-> FALSE]
    /\ clients = [cid \in Clients |-> InitClient(cid)]
    /\ crashes = 0

Next ==
    \* Bookies
    \/ BookieSendsAddConfirmedResponse
    \/ BookieSendsAddFencedResponse
    \/ BookieSendsFencingReadLacResponse
    \/ BookieSendsReadResponse
    \/ BookieCrashesWhenLedgerOpen
    \/ BookieCrashesWhenLedgerInRecovery
    \/ BookieCrashesWhenLedgerClosed
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
        \/ ClientSendsReadRequests(cid)
        \/ ClientReceivesNonFinalRead(cid)
        \/ ClientCompletesReadSuccessfully(cid)
        \/ ClientCompletesReadWithNoSuchEntry(cid)
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
    /\ b_limbo \in [Bookies -> BOOLEAN]
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
\* Last modified Sun Nov 21 14:00:47 CET 2021 by GUNMETAL
\* Last modified Thu Apr 29 17:55:12 CEST 2021 by jvanlightly
