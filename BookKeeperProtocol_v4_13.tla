------------------------- MODULE BookKeeperProtocol_v4_13 -------------------------
EXTENDS MessagePassing_v4_13, Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
This specification is refers to released version 4.13.

See the readme for more information.
*)

\* Input parameters
CONSTANTS Bookies,                      \* The bookies available e.g. { B1, B2, B3, B4 }
          WriteQuorum,                  \* The replication factor under normal circumstances
          AckQuorum,                    \* The number of bookies required to acknowledge an entry for the
                                        \* writer to acknowledge to its own client, also the minimum
                                        \* replication factor (can occur in scenarios such as ensemble change or ledger closes)
          SendLimit,                    \* The data items to send. Limited to a very small number of data items
                                        \* in order to keep the state space small. E.g 2
          RecoveryReadsFence            \* TRUE|FALSE for whether recovery reads also fence.
                                        \* Currently BK does not fence on recovery reads. See defects in readme.


\* Model values
CONSTANTS Nil,
          STATUS_OPEN,
          STATUS_IN_RECOVERY,
          STATUS_CLOSED,
          STATUS_INVALID

\* Ledger state in the metadata store
VARIABLES meta_status,              \* the ledger status
          meta_fragments,           \* ledger fragments
          meta_last_entry,          \* the endpoint of the ledger
          meta_version              \* ledger metatdata version

\* Bookie state (each is a function whose domain is the set of bookies) pertaining to this single ledger
VARIABLES b_entries,                \* the entries stored in each bookie
          b_fenced,                 \* the fenced status of each bookie (TRUE/FALSE)
          b_lac                     \* the last add confirmed of each bookie

\* the state of the two writers
VARIABLES w1,
          w2

ASSUME SendLimit \in Nat
ASSUME SendLimit > 0
ASSUME RecoveryReadsFence \in BOOLEAN
ASSUME WriteQuorum \in Nat
ASSUME WriteQuorum > 0
ASSUME AckQuorum \in Nat
ASSUME AckQuorum > 0
ASSUME WriteQuorum >= AckQuorum


bookie_vars == << b_fenced, b_entries, b_lac >>
meta_vars == << meta_status, meta_fragments, meta_last_entry, meta_version >>
vars == << bookie_vars, w1, w2, meta_vars, messages >>

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

WriterStatuses ==
    {Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED, STATUS_INVALID}

WriterState ==
    [meta_version: Nat \union {Nil},            \* The metadata version this writer has
     status: WriterStatuses,                    \* The possible statuses of a writer
     curr_fragment: Fragment \union {Nil},      \* The current fragment known by a writer
     pending_add_ops: SUBSET PendingAddOp,      \* The pending add operations of a writer
     lap: Nat,                                  \* The Last Add Pushed of a writer
     lac: Nat,                                  \* The Last Add Confirmed of a writer
     confirmed: [EntryIds -> SUBSET Bookies],   \* The bookies that have confirmed each entry id
     fenced: SUBSET Bookies,                    \* The bookies that have confirmed they are fenced to this writer
     curr_read_entry: Entry \union {Nil},       \* The entry currently being read (during recovery)
     has_entry: SUBSET Bookies,                 \* Which bookies confirmed they have the current entry being read
     no_such_entry: SUBSET Bookies,             \* Which bookies confirmed they do not have the current entry being read
     recovery_phase: 0..WritePhase]             \* The recovery phase (an artifical phase for reducing state space)

\* Each writer starts empty, no state
InitWriter ==
    [meta_version    |-> Nil,
     status          |-> Nil,
     curr_fragment   |-> Nil,
     pending_add_ops |-> {},
     lap             |-> 0,
     lac             |-> 0,
     confirmed       |-> [id \in EntryIds |-> {}],
     fenced          |-> {},
     curr_read_entry |-> Nil,
     has_entry       |-> {},
     no_such_entry   |-> {},
     recovery_phase  |-> 0]

(***************************************************************************)
(* Fragment Helpers                                                        *)
(***************************************************************************)

CurrentFragment ==
    Last(meta_fragments)

FragmentOf(fragment_id) ==
    meta_fragments[fragment_id]

FragmentOfEntryId(entry_id) ==
    IF Len(meta_fragments) = 1
    THEN meta_fragments[1]
    ELSE IF Last(meta_fragments).first_entry_id <= entry_id
         THEN Last(meta_fragments)
         ELSE
            LET f_id == CHOOSE f1 \in DOMAIN meta_fragments :
                            \E f2 \in DOMAIN meta_fragments :
                                /\ meta_fragments[f1].id = meta_fragments[f2].id-1
                                /\ meta_fragments[f1].first_entry_id <= entry_id
                                /\ meta_fragments[f2].first_entry_id > entry_id
            IN meta_fragments[f_id]

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
(* BY: writer1                                                             *)
(*                                                                         *)
(* A ledger is created with an ensemble that is selected                   *)
(* non-deterministically.                                                  *)
(***************************************************************************)

W1CreatesLedger ==
    /\ meta_status = Nil
    /\ w1.meta_version = Nil
    /\ LET fragment == [id |-> 1, ensemble |-> SelectEnsemble({},{}), first_entry_id |-> 1]
       IN
        /\ w1' = [w1 EXCEPT !.status = STATUS_OPEN,
                            !.meta_version = 1,
                            !.curr_fragment = fragment]
        /\ meta_status' = STATUS_OPEN
        /\ meta_version' = 1
        /\ meta_fragments' = Append(meta_fragments, fragment)
    /\ UNCHANGED << bookie_vars, w2, meta_last_entry, messages >>

(***************************************************************************)
(* ACTION: Send Add Entry Requests for a given data item                   *)
(* BY: writer1                                                             *)
(*                                                                         *)
(* The writer sends an AddEntryRequestMessage to each bookie of the        *)
(* current fragment ensemble for a data item not yet sent.                 *)
(***************************************************************************)

GetAddEntryRequests(writer, entry, ensemble, recovery) ==
    { [type     |-> AddEntryRequestMessage,
       bookie   |-> b,
       entry    |-> entry,
       lac      |-> writer.lac,
       recovery |-> recovery] : b \in ensemble }

SendAddEntryRequests(entry) ==
    /\ SendMessagesToEnsemble(GetAddEntryRequests(w1,
                                                  entry,
                                                  w1.curr_fragment.ensemble,
                                                  FALSE))
    /\ w1' = [w1 EXCEPT !.lap = entry.id,
                        !.pending_add_ops = @ \union {[entry       |-> entry,
                                                       fragment_id |-> w1.curr_fragment.id,
                                                       ensemble    |-> w1.curr_fragment.ensemble]}]

W1SendsAddEntryRequests ==
    /\ w1.status = STATUS_OPEN
    /\ LET entry_data == w1.lap + 1
       IN
        /\ entry_data <= SendLimit
        /\ SendAddEntryRequests([id   |-> entry_data, data |-> entry_data])
    /\ UNCHANGED << bookie_vars, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Receive an AddEntryRequestMessage, Send a confirm               *)
(* BY: a bookie                                                            *)
(*                                                                         *)
(* A bookie receives a AddEntryRequestMessage, the ledger is not fenced so *)
(* it adds the entry and responds with a success response.                 *)
(***************************************************************************)

GetAddEntryResponse(add_entry_msg, success) ==
    [type     |-> AddEntryResponseMessage,
     bookie   |-> add_entry_msg.bookie,
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
        /\ UNCHANGED << b_fenced, w1, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Receive an AddEntryRequestMessage, Send a fenced response       *)
(* BY: a bookie                                                            *)
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
        /\ UNCHANGED << bookie_vars, w1, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a success AddEntryResponseMessage                       *)
(* BY: writer1 or writer2                                                  *)
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

AddToConfirmed(writer, entry_id, bookie) ==
    [writer.confirmed EXCEPT ![entry_id] = @ \union {bookie}]

\* Only remove if it has reached the Ack Quorum and <= LAC
MayBeRemoveFromPending(writer, confirmed, lac) ==
    { op \in writer.pending_add_ops :
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

ReceiveAddConfirmedResponse(writer, is_recovery) ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = is_recovery
        /\ msg.success = TRUE
        /\ msg.bookie \in writer.curr_fragment.ensemble
        /\ LET confirmed == AddToConfirmed(writer, msg.entry.id, msg.bookie)
           IN LET lac == MaxContiguousConfirmedEntry(confirmed)
              IN
                writer' = [writer EXCEPT !.confirmed = confirmed,
                                         !.lac = IF lac > @ THEN lac ELSE @,
                                         !.pending_add_ops = MayBeRemoveFromPending(writer, confirmed, lac)]
        /\ MessageProcessed(msg)


W1ReceivesAddConfirmedResponse ==
    /\ w1.status = STATUS_OPEN
    /\ ReceiveAddConfirmedResponse(w1, FALSE)
    /\ UNCHANGED << bookie_vars, w2, meta_vars >>

W2ReceivesAddConfirmedResponse ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ ReceiveAddConfirmedResponse(w2, TRUE)
    /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a fenced AddEntryResponseMessage                        *)
(* BY: writer1                                                             *)
(*                                                                         *)
(* The writer receives a fenced AddEntryResponseMessage which means ledger *)
(* recovery has been initiated and the ledger has been fenced on that      *)
(* bookie.                                                                 *)
(* Therefore the client ceases further interactions (outside of the spec   *)
(* it would check it is still the leader and try and open a new ledger     *)
(* (with fencing).                                                         *)
(***************************************************************************)

W1ReceivesAddFencedResponse ==
    /\ w1.status = STATUS_OPEN
    /\ \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = FALSE
        /\ msg.success = FALSE
        /\ msg.bookie \in w1.curr_fragment.ensemble
        /\ w1' = [w1 EXCEPT !.status = Nil]
        /\ MessageProcessed(msg)
        /\ UNCHANGED << bookie_vars, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Change Ensemble                                                 *)
(* BY: writer1 or writer 2                                                             *)
(*                                                                         *)
(* A write to a bookie has failed (in this spec due to timeout).           *)
(* The writer:                                                             *)
(*  - opens a new fragment with a new ensemble, with its first entry id    *)
(*    being LAC + 1.                                                       *)
(*  - removes the failed bookie from the confirmed set of any non-committed*)
(*    entries. For entries that have Ack Quorum but are ahead of the LAC,  *)
(*    and therefore not committed, this can reduce them back down to       *)
(*    below AckQuorum.                                                     *)
(*                                                                         *)
(* NOTE1: we don't need to model the writer closing the ledger at this     *)
(*       point due no other ensembles being available because this spec    *)
(*       allows the writer to close the ledger at any time anyway.         *)
(*                                                                         *)
(* NOTE2: Before triggering another ensemble change, we ensure that all    *)
(*        pending add ops that need to be sent to bookies due to a prior   *)
(*        ensemble change, do get sent first                               *)
(***************************************************************************)

NoPendingResends(writer) ==
    ~\E op \in writer.pending_add_ops :
        /\ \/ op.fragment_id # writer.curr_fragment.id
           \/ op.ensemble # writer.curr_fragment.ensemble

\* The next fragment is only valid if it's first_entry_id is equal to or higher than all existing fragments.
ValidNextFragment(first_entry_id) ==
    ~\E i \in DOMAIN meta_fragments : meta_fragments[i].first_entry_id > first_entry_id

\* if there already exists an ensemble with the same first_entry_id the replace it,
\* else append a new fragment
UpdatedFragments(writer, first_entry_id, new_ensemble) ==
    IF first_entry_id = writer.curr_fragment.first_entry_id
    THEN [index \in DOMAIN meta_fragments |-> IF meta_fragments[index] = CurrentFragment
                                              THEN [meta_fragments[index] EXCEPT !.ensemble = new_ensemble]
                                              ELSE meta_fragments[index]]
    ELSE Append(meta_fragments, [id             |-> Len(meta_fragments)+1,
                                 ensemble       |-> new_ensemble,
                                 first_entry_id |-> first_entry_id])

ChangeEnsemble(writer, recovery) ==
    /\ NoPendingResends(writer)
    /\ writer.meta_version = meta_version
    /\ \E bookie \in writer.curr_fragment.ensemble :
        /\ WriteTimeoutForBookie(messages, bookie, recovery)
        /\ EnsembleAvailable(writer.curr_fragment.ensemble \ {bookie}, {bookie})
        /\ ValidNextFragment(writer.lac + 1)
        /\ LET new_ensemble   == SelectEnsemble(writer.curr_fragment.ensemble \ {bookie}, {bookie})
               first_entry_id == writer.lac + 1
           IN LET updated_fragments == UpdatedFragments(writer, first_entry_id, new_ensemble)
              IN
                /\ meta_fragments' = updated_fragments
                /\ meta_version' = meta_version + 1
                /\ writer' = [writer EXCEPT !.meta_version = meta_version + 1,
                                            !.confirmed = [id \in DOMAIN writer.confirmed |->
                                                               IF id >= first_entry_id
                                                               THEN writer.confirmed[id] \ {bookie}
                                                               ELSE writer.confirmed[id]],
                                            !.curr_fragment = Last(updated_fragments)]
                /\ ClearWriteTimeout(bookie, recovery)

W1ChangesEnsemble ==
    /\ w1.status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ ChangeEnsemble(w1, FALSE)
    /\ UNCHANGED <<  bookie_vars, w2, meta_status, meta_last_entry >>

W2ChangesEnsemble ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ meta_status = STATUS_IN_RECOVERY
    /\ ChangeEnsemble(w2, TRUE)
    /\ UNCHANGED <<  bookie_vars, w1, meta_status, meta_last_entry >>

(***************************************************************************)
(* ACTION: Invalid Ensemble Change                                         *)
(* BY: writer1 or writer 2                                                 *)
(*                                                                         *)
(* An ensemble change is triggered but the first entry id is lower than an *)
(* existing ensemble, which is an invalid change not permitted by the      *)
(* protocol.                                                               *)
(***************************************************************************)

InvalidEnsembleChange(writer, recovery) ==
    /\ NoPendingResends(writer)
    /\ writer.meta_version = meta_version
    /\ \E bookie \in writer.curr_fragment.ensemble :
        /\ WriteTimeoutForBookie(messages, bookie, recovery)
        /\ EnsembleAvailable(writer.curr_fragment.ensemble \ {bookie}, {bookie})
        /\ ~ValidNextFragment(writer.lac + 1)
        /\ writer' = [writer EXCEPT !.status = STATUS_INVALID]

W1TriesInvalidEnsembleChange ==
    /\ w1.status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ InvalidEnsembleChange(w1, FALSE)
    /\ UNCHANGED <<  bookie_vars, w2, meta_vars, messages >>

W2TriesInvalidEnsembleChange ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ meta_status = STATUS_IN_RECOVERY
    /\ InvalidEnsembleChange(w2, TRUE)
    /\ UNCHANGED <<  bookie_vars, w1, meta_vars, messages >>

(***************************************************************************)
(* ACTION: Send Pending Add Op                                             *)
(* BY: writer1 or writer 2                                                 *)
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
SetNewEnsemble(writer, pending_op) ==
    {
        IF op = pending_op
        THEN [entry       |-> op.entry,
              fragment_id |-> writer.curr_fragment.id,
              ensemble    |-> writer.curr_fragment.ensemble]
        ELSE op : op \in writer.pending_add_ops
    }

\* send the add to any bookies in the new ensemble that are not in the original
\* then update the op with the new ensemble.
SendPendingAddOp(writer, is_recovery) ==
    /\ \E op \in writer.pending_add_ops :
        /\ \/ op.fragment_id # writer.curr_fragment.id
           \/ op.ensemble # writer.curr_fragment.ensemble
        /\ ~\E op2 \in writer.pending_add_ops :
            /\ op2.fragment_id = op.fragment_id
            /\ op2.ensemble = op.ensemble
            /\ op2.entry.id < op.entry.id
        /\ LET new_bookies == writer.curr_fragment.ensemble \ op.ensemble
           IN
              /\ SendMessagesToEnsemble(GetAddEntryRequests(writer,
                                                            op.entry,
                                                            new_bookies,
                                                            is_recovery))
              /\ writer' = [writer EXCEPT !.pending_add_ops = SetNewEnsemble(writer, op)]

W1SendsPendingAddOp ==
    /\ w1.status = STATUS_OPEN
    /\ SendPendingAddOp(w1, FALSE)
    /\ UNCHANGED << bookie_vars, w2, meta_vars >>

W2SendsPendingAddOp ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ SendPendingAddOp(w2, TRUE)
    /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: Close the ledger                                                *)
(* BY: writer1                                                             *)
(*                                                                         *)
(* The writer decides to close the ledger. The metadata store still        *)
(* has the ledger as open so the close succeeds.                           *)
(* A close can happen at any time.                                         *)
(***************************************************************************)

W1CloseLedgerSuccess ==
    /\ w1.meta_version = meta_version
    /\ w1.status = STATUS_OPEN
    /\ meta_status = STATUS_OPEN
    /\ w1' = [w1 EXCEPT !.meta_version = @ + 1,
                        !.status = STATUS_CLOSED]
    /\ meta_status' = STATUS_CLOSED
    /\ meta_last_entry' = w1.lac
    /\ meta_version' = meta_version + 1
    /\ UNCHANGED << bookie_vars, w2, meta_fragments, messages >>

(***************************************************************************)
(* ACTION: Closing the ledger fails                                        *)
(* BY: writer1                                                             *)
(*                                                                         *)
(* The writer decides to close the ledger. The metadata store has the      *)
(* ledger as not open so the close fails and the client ceases further     *)
(* interactions with this ledger (we do not model a stalled recovery).     *)
(***************************************************************************)

W1CloseLedgerFail ==
    /\ w1.meta_version # meta_version
    /\ w1.status = STATUS_OPEN
    /\ meta_status # STATUS_OPEN
    /\ w1' = [w1 EXCEPT !.meta_version = Nil]
    /\ UNCHANGED << bookie_vars, w2, meta_vars, messages >>

(***************************************************************************)
(* ACTION: Start ledger recovery                                           *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* A second client decides to start the recovery process for the ledger.   *)
(* Changes the meta status to IN_RECOVERY and sends a fencing read LAC     *)
(* request to each bookie in the current ensemble.                         *)
(* BY: a second client                                                     *)
(*                                                                         *)
(***************************************************************************)
(***************************************************************************)

GetFencedReadLacRequests(ensemble) ==
    { [type   |-> FenceRequestMessage,
       bookie |-> bookie] : bookie \in ensemble }

W2PlaceInRecovery ==
    /\ w2.status = Nil
    /\ meta_status = STATUS_OPEN
    /\ meta_status' = STATUS_IN_RECOVERY
    /\ meta_version' = meta_version + 1
    /\ w2' = [w2 EXCEPT !.status         = STATUS_IN_RECOVERY,
                        !.meta_version   = meta_version + 1,
                        !.recovery_phase = FencingPhase,
                        !.curr_fragment  = CurrentFragment]
    /\ SendMessagesToEnsemble(GetFencedReadLacRequests(CurrentFragment.ensemble))
    /\ UNCHANGED << bookie_vars, w1, meta_fragments, meta_last_entry >>

(***************************************************************************)
(* ACTION: Receive a fence request, send a response                        *)
(* BY: a bookie                                                            *)
(*                                                                         *)
(* A bookie receives a fencing read LAC request and sends back a success   *)
(* response with its LAC. We only model a single second writer, so this    *)
(* will only happen once per bookie (of current ensemble).                 *)
(***************************************************************************)

GetFencingReadLacResponseMessage(msg) ==
    [type   |-> FenceResponseMessage,
     bookie |-> msg.bookie,
     lac    |-> b_lac[msg.bookie]]

BookieSendsFencingReadLacResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, FenceRequestMessage)
        /\ b_fenced' = [b_fenced EXCEPT ![msg.bookie] = TRUE]
        /\ ProcessedOneAndSendAnother(msg, GetFencingReadLacResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, w1, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a fence response                                        *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* The second writer receives a success FenceResponseMessage               *)
(* and takes note of the bookie that confirmed its fenced status and if    *)
(* its LAC is highest, stores it.                                          *)
(* Once the read phase has started any late arriving LAC reads are ignored.*)
(***************************************************************************)

NotStartedReadPhase ==
    ~\E msg \in DOMAIN messages :
        msg.type = ReadRequestMessage

W2ReceivesFencingReadLacResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, FenceResponseMessage)
        /\ LET lac == IF msg.lac > w2.curr_fragment.first_entry_id - 1
                      THEN msg.lac
                      ELSE w2.curr_fragment.first_entry_id - 1
           IN
            /\ w2' = [w2 EXCEPT !.fenced = @ \union {msg.bookie},
                                !.lac = IF NotStartedReadPhase /\ (w2.lac = Nil \/ lac > w2.lac)
                                        THEN lac
                                        ELSE @,
                                !.lap = IF NotStartedReadPhase /\ (w2.lac = Nil \/ lac > w2.lac)
                                        THEN lac
                                        ELSE @]
            /\ MessageProcessed(msg)
            /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: Send a recovery read request to each bookie                     *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* The second writer sends a ReadRequestMessage to each bookie of the      *)
(* current ensemble once every ack quorum has at least one fenced bookie.  *)
(*                                                                         *)
(* NOTE1: The spec allows recovery read requests to fence the ledger via   *)
(*        the use of the RecoveryReadsFence constant.                      *)
(* NOTE2: Remember that entry ids start at 1 in this spec as TLA+ is base 1*)
(***************************************************************************)

NotSentRead(entry_id) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = ReadRequestMessage
        /\ msg.entry_id = entry_id

GetRecoveryReadRequests(entry_id, ensemble) ==
    { [type     |-> ReadRequestMessage,
       bookie   |-> b,
       entry_id |-> entry_id,
       fence    |-> RecoveryReadsFence] : b \in ensemble }

W2SendsReadRequests ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ \/ w2.recovery_phase = ReadPhase
       \/ /\ w2.recovery_phase = FencingPhase
          /\ \A ack_quorum \in { s \in SUBSET w2.curr_fragment.ensemble : Cardinality(s) = AckQuorum } :
                w2.fenced \intersect ack_quorum # {}
    /\ LET next_entry_id == w2.lap+1
       IN
        /\ NotSentRead(next_entry_id)
        /\ w2' = [w2 EXCEPT !.recovery_phase = PendingReadResponsePhase]
        /\ SendMessagesToEnsemble(GetRecoveryReadRequests(next_entry_id, FragmentOfEntryId(next_entry_id).ensemble))
        /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a read request, send a response                         *)
(* BY: a bookie                                                            *)
(*                                                                         *)
(* A bookie receives a ReadRequestMessage and sends back a success         *)
(* response if it has the entry and a non-success if it doesn't.           *)
(*                                                                         *)
(* NOTE: The spec allows recovery read requests to fence the ledger via    *)
(*       the use of the RecoveryReadsFence constant.                       *)
(***************************************************************************)

GetReadResponseMessage(msg) ==
    [type     |-> ReadResponseMessage,
     bookie   |-> msg.bookie,
     entry    |-> IF \E entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  THEN CHOOSE entry \in b_entries[msg.bookie] : entry.id = msg.entry_id
                  ELSE Nil,
     fence    |-> msg.fence]

BookieSendsReadResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadRequestMessage)
        /\ IF msg.fence = TRUE
           THEN b_fenced' = [b_fenced EXCEPT ![msg.bookie] = TRUE]
           ELSE UNCHANGED b_fenced
        /\ ProcessedOneAndSendAnother(msg, GetReadResponseMessage(msg))
        /\ UNCHANGED << b_entries, b_lac, w1, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Receive a non final read response                               *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* The second writer receives either a success ReadResponseMessage         *)
(* or a NoSuchEntry (entry=Nil). This action occurs when there are still   *)
(* more responses pending (including timeouts).                            *)
(***************************************************************************)

ReceivedAllResponses(has_entry, no_such_entry, ensemble) ==
    Cardinality(has_entry) + Cardinality(no_such_entry) + ReadTimeoutCount(ensemble, TRUE) = WriteQuorum

NotEnoughBookies(no_such_entry) ==
    Cardinality(no_such_entry) >= (WriteQuorum - AckQuorum) + 1

EnoughBookies(has_entry) ==
    Cardinality(has_entry) >= AckQuorum

ReadSuccess(read_ensemble, has_entry, no_such_entry) ==
   IF /\ ReceivedAllResponses(has_entry, no_such_entry, read_ensemble)
      /\ EnoughBookies(has_entry)
   THEN TRUE
   ELSE FALSE

ReadIsNoSuchEntry(read_ensemble, has_entry, no_such_entry) ==
    IF /\ ReceivedAllResponses(has_entry, no_such_entry, read_ensemble)
       /\ NotEnoughBookies(no_such_entry)
    THEN TRUE
    ELSE FALSE

W2ReceivesNonFinalRead ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
        /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id).ensemble ELSE {}
               has_entry     == IF msg.entry # Nil THEN w2.has_entry \union {msg.bookie} ELSE w2.has_entry
               no_such_entry == IF msg.entry = Nil THEN w2.no_such_entry \union {msg.bookie} ELSE w2.no_such_entry
           IN /\ ~ReceivedAllResponses(has_entry, no_such_entry, read_ensemble)
              /\ w2' = [w2 EXCEPT !.has_entry       = has_entry,
                                  !.no_such_entry   = no_such_entry,
                                  !.curr_read_entry = IF msg.entry # Nil THEN msg.entry ELSE @,
                                  !.fenced          = IF msg.fence = TRUE THEN @ \union {msg.bookie} ELSE @]
              /\ MessageProcessed(msg)
        /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: A read completes successfullly.                                 *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* The second writer receives a read such that:                            *)
(* 1. all responses have either been received or have timed out            *)
(* 2. there are enough bookies to count as a successful read               *)
(* More read requests will subsequently be sent out.                       *)
(***************************************************************************)
W2CompletesReadSuccessfully ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
        /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id).ensemble ELSE {}
               has_entry     == IF msg.entry # Nil THEN w2.has_entry \union {msg.bookie} ELSE w2.has_entry
               no_such_entry == IF msg.entry = Nil THEN w2.no_such_entry \union {msg.bookie} ELSE w2.no_such_entry
           IN /\ ReadSuccess(read_ensemble, has_entry, no_such_entry)
              /\ LET entry_data == IF msg.entry = Nil THEN w2.curr_read_entry.data ELSE msg.entry.data
                 IN
                  /\ w2' = [w2 EXCEPT !.has_entry       = {}, \* reset for next read
                                      !.no_such_entry   = {}, \* reset for next read
                                      !.curr_read_entry = Nil, \* reset for next read
                                      !.fenced          = IF msg.fence = TRUE THEN @ \union {msg.bookie} ELSE @,
                                      !.lap             = @ + 1,
                                      !.pending_add_ops = @ \union {[entry       |-> [id   |-> w2.lap + 1,
                                                                                      data |-> entry_data],
                                                                     fragment_id |-> w2.curr_fragment.id,
                                                                     ensemble    |-> w2.curr_fragment.ensemble]},
                                      !.recovery_phase  = ReadPhase]
              /\ ClearReadTimeouts(msg, read_ensemble)
        /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: A read completes with NoSuchEntry/Ledger.                       *)
(* BY: writer 2                                                            *)
(*                                                                         *)
(* The second writer receives a read such that:                            *)
(* 1. all responses have either been received or have timed out            *)
(* 2. there are not enough bookies to count as a successful read           *)
(*    NOTE: this is an explicit count of those that confirmed they do not  *)
(*          have the entry. Time outs do not count.                        *)
(* This concludes the read phase. Note that the protocol runs the reads    *)
(* and write concurrently. This spec separates them to reduce the state    *)
(* space.                                                                  *)
(***************************************************************************)

W2CompletesReadWithNoSuchEntry ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
        /\ LET read_ensemble == IF msg.entry # Nil THEN FragmentOfEntryId(msg.entry.id).ensemble ELSE {}
               has_entry     == IF msg.entry # Nil THEN w2.has_entry \union {msg.bookie} ELSE w2.has_entry
               no_such_entry == IF msg.entry = Nil THEN w2.no_such_entry \union {msg.bookie} ELSE w2.no_such_entry
           IN
              /\ ReadIsNoSuchEntry(read_ensemble, has_entry, no_such_entry)
              /\ w2' = [w2 EXCEPT !.has_entry       = {}, \* reset to reduce state space
                                  !.no_such_entry   = {}, \* reset to reduce state space
                                  !.curr_read_entry = Nil, \* reset to reduce state space
                                  !.fenced          = IF msg.fence = TRUE
                                                      THEN @ \union {msg.bookie}
                                                      ELSE @,
                                  !.recovery_phase  = WritePhase]
              /\ ClearReadTimeouts(msg, read_ensemble)
        /\ UNCHANGED << bookie_vars, w1, meta_vars >>

(***************************************************************************)
(* ACTION: Write back a entry that was successfully read.                  *)
(* BY: writer2                                                             *)
(*                                                                         *)
(* Writes follow the same logic as replication writes, in that they can    *)
(* involves the creation of new fragments. Also note that all entries are  *)
(* written to the current fragment, not the fragment they were read from.  *)
(***************************************************************************)

NotSentWrite(op) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = AddEntryRequestMessage
        /\ msg.recovery = TRUE
        /\ msg.entry = op.entry

W2WritesBackEntry ==
    /\ w2.status = STATUS_IN_RECOVERY
    /\ w2.recovery_phase = WritePhase
    /\ \E op \in w2.pending_add_ops :
        /\ NotSentWrite(op)
        /\ ~\E op2 \in w2.pending_add_ops :
            /\ NotSentWrite(op2)
            /\ op2.entry.id < op.entry.id
        /\ SendMessagesToEnsemble(GetAddEntryRequests(w2,
                                                      op.entry,
                                                      w2.curr_fragment.ensemble,
                                                      TRUE))
   /\ UNCHANGED << bookie_vars, w1, w2, meta_vars >>

(***************************************************************************)
(* ACTION: Close the ledger upon successfully completing all writes.       *)
(* BY: writer2                                                             *)
(*                                                                         *)
(* Once all the entries that were read during recovery have been           *)
(* successfully written back. Close the ledger.                            *)
(* In the protocol, any new ensembles are written to the metadata store in *)
(* a CAS operation. In this spec, the ensembles are written immediately    *)
(* because we only model one second writer and we can reuse more TLA+.     *)
(***************************************************************************)

W2ClosesLedger ==
    /\ meta_version = w2.meta_version
    /\ meta_status = STATUS_IN_RECOVERY
    /\ w2.status = STATUS_IN_RECOVERY
    /\ w2.recovery_phase = WritePhase
    /\ Cardinality(w2.pending_add_ops) = 0
    /\ w2' = [w2 EXCEPT !.status = STATUS_CLOSED,
                        !.meta_version = @ + 1]
    /\ meta_version' = meta_version + 1
    /\ meta_status' = STATUS_CLOSED
    /\ meta_last_entry' = w2.lac
    /\ UNCHANGED << bookie_vars, w1, meta_fragments, messages >>

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
    /\ w1 = InitWriter
    /\ w2 = InitWriter

Next ==
    \* Bookies
    \/ BookieSendsAddConfirmedResponse
    \/ BookieSendsAddFencedResponse
    \/ BookieSendsFencingReadLacResponse
    \/ BookieSendsReadResponse
    \* W1
    \/ W1CreatesLedger
    \/ W1SendsAddEntryRequests
    \/ W1ReceivesAddConfirmedResponse
    \/ W1ReceivesAddFencedResponse
    \/ W1ChangesEnsemble
    \/ W1TriesInvalidEnsembleChange
    \/ W1SendsPendingAddOp
    \/ W1CloseLedgerSuccess
    \/ W1CloseLedgerFail
    \* W2
    \/ W2PlaceInRecovery
    \/ W2ReceivesFencingReadLacResponse
    \/ W2SendsReadRequests
    \/ W2ReceivesNonFinalRead
    \/ W2CompletesReadSuccessfully
    \/ W2CompletesReadWithNoSuchEntry
    \/ W2WritesBackEntry
    \/ W2ReceivesAddConfirmedResponse
    \/ W2ChangesEnsemble
    \/ W2TriesInvalidEnsembleChange
    \/ W2SendsPendingAddOp
    \/ W2ClosesLedger


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
    /\ w1 \in WriterState
    /\ w2 \in WriterState

(***************************************************************************)
(* Invariant: No Divergence Between Writer And MetaData                    *)
(*                                                                         *)
(* This invariant is violated if, once a ledger is closed, the writer has  *)
(* an entry acknowledged (by Qa bookies) that has a higher entry id than   *)
(* the endpoint of the ledger as stored in the metadata store.             *)
(* This is divergence and data loss.                                       *)
(***************************************************************************)
NoDivergenceBetweenWriterAndMetaData ==
    IF meta_status # STATUS_CLOSED
    THEN TRUE
    ELSE \A id \in 1..w1.lac :
            id <= meta_last_entry

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
                LET fragment == FragmentOfEntryId(id)
                IN EntryIdReachesAckQuorum(fragment.ensemble, id)
         ELSE TRUE

(***************************************************************************)
(* Invariant: New fragments cannot have a lower first entry id than any    *)
(*            existing fragment.                                           *)
(*                                                                         *)
(* This invariant is violated when a writer goes to add a fragment to the  *)
(* metadata store that is invalid.                                         *)
(***************************************************************************)
OnlyValidFragments ==
    /\ w1.status # STATUS_INVALID
    /\ w2.status # STATUS_INVALID

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
    /\ w1.status = STATUS_CLOSED

Liveness ==
    /\ WF_vars(Next)
    /\ []<>LedgerIsClosed

Spec == Init /\ [][Next]_vars


=============================================================================
\* Modification History
\* Last modified Mon Nov 22 10:23:03 CET 2021 by GUNMETAL
\* Last modified Tue Dec 01 13:57:30 CET 2020 by jvanlightly
\* Created Tue Nov 10 13:36:16 CET 2020 by jvanlightly
