--------------------------- MODULE LedgerChaining ---------------------------
EXTENDS Integers, FiniteSets, Sequences, SequencesExt, TLC

(*
This specification models how ledgers can be chained to form a single log.

It models a pool of clients ready to take leadership and perform writes to the segmented log.
When a client gets elected as the leader, it:
1. closes the current ledger
2. creates a new ledger
3. appends the ledger to the ledger list
4. starts writing to the ledger

Leadership can change at anytime and the mechanics of leader election nor failure detection are not included.
*)

\* the set of all clients
CONSTANTS Clients
          
\* the various states a client can be in (model values)
CONSTANTS WAITING,
          GET_MD_FOR_CLOSING,
          CLOSE_LAST_LEDGER,
          PENDING_CREATE_LEDGER,
          PENDING_APPEND_LEDGER,
          HAS_OPEN_LEDGER
                 
\* client state
VARIABLES c_state

\* metadata store state
VARIABLES md_ll,
          md_ll_version,
          md_ledgers,
          md_leader,
          md_next_lid

\* the ledgers that have been written to
VARIABLES written_ledgers
          
vars == << c_state, md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>        

NoLedger == [id |-> 0, open |-> FALSE, version |-> -1]

(*
    Starts with no leader and no ledgers
*)
Init ==
    /\ c_state = [c \in Clients |-> [leader     |-> FALSE,
                                     status     |-> WAITING,
                                     ll_version |-> -1,
                                     ledger     |-> NoLedger]]
    /\ md_leader = CHOOSE c \in Clients : TRUE
    /\ md_ll_version = 0
    /\ md_ll = <<>>
    /\ md_ledgers = <<>>
    /\ md_next_lid = 1
    /\ written_ledgers = {}

(*
    A leader is elected by the metadata store
*)
LeaderChosen(c) ==
    /\ md_leader # c
    /\ md_leader' = c
    /\ UNCHANGED << c_state, md_ll, md_ll_version, md_ledgers, md_next_lid, written_ledgers >>

(*
    A client becomes aware it is the leader and assumes that role
*)
BecomeLeader(c) ==
    /\ c_state[c].leader = FALSE
    /\ md_leader = c
    /\ c_state' = [c_state EXCEPT ![c].leader = TRUE,
                                  ![c].status = GET_MD_FOR_CLOSING]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>

(*
    A client that believes it is the leader becomes aware it is not the leader anymore and returns to WAITING.
    It does not need to close the ledger, though it could, as another client becoming the leader will do that.
*)
Abdicate(c) ==
    /\ c_state[c].leader = TRUE
    /\ md_leader # c
    /\ c_state' = [c_state EXCEPT ![c].leader = FALSE,
                                  ![c].status = WAITING]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>

(* 
    A newly elected leader must first obtain the metadata of the ledger list and the 
    last ledger in the ledger list.
    If the ledger list is empty, it transitions to the PENDING_CREATE_LEDGER state, else
    moves to the PENDING_CREATE_LEDGER state.
    The version of the ledger list is cached now which is important as any change made by another
    client in the meantime will be detected. 
*)
GetLastLedger(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = GET_MD_FOR_CLOSING
    /\ \/ /\ md_ll # <<>>
          /\ c_state' = [c_state EXCEPT ![c].ll_version = md_ll_version,
                                        ![c].ledger     = md_ledgers[Last(md_ll)],
                                        ![c].status     = CLOSE_LAST_LEDGER]
       \/ /\ md_ll = <<>>
          /\ c_state' = [c_state EXCEPT ![c].ll_version = md_ll_version,
                                        ![c].status     = PENDING_CREATE_LEDGER]                                 
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >> 

(*
    The client leader sees that the last ledger is already closed, so moves to the PENDING_CREATE_LEDGER state.
*)    
LedgerAlreadyClosed(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = CLOSE_LAST_LEDGER
    /\ c_state[c].ledger.open = FALSE
    /\ c_state' = [c_state EXCEPT ![c].status = PENDING_CREATE_LEDGER]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>

(*
    The client leader closes the last ledger.
*)
CloseLastLedgerSuccess(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = CLOSE_LAST_LEDGER
    /\ c_state[c].ledger.open = TRUE
    /\ LET ledger_id == c_state[c].ledger.id
       IN
            /\ c_state[c].ledger.version = md_ledgers[ledger_id].version
            /\ md_ledgers' = [md_ledgers EXCEPT ![ledger_id].open = FALSE,
                                                ![ledger_id].version = @ + 1]
            /\ c_state' = [c_state EXCEPT ![c].status = PENDING_CREATE_LEDGER]
    /\ UNCHANGED << md_ll, md_ll_version, md_leader, md_next_lid, written_ledgers >>
    
(*
    The client leader tries to close the last ledger, but another client has updated the
    ledger metadata in the meantime. The leader backs off and returns to the GET_MD_FOR_CLOSING
    state.
*)    
CloseLastLedgerBadVersion(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = CLOSE_LAST_LEDGER
    /\ c_state[c].ledger.open = TRUE
    /\ c_state[c].ledger.version < md_ledgers[c_state[c].ledger.id].version
    /\ c_state' = [c_state EXCEPT ![c].status = GET_MD_FOR_CLOSING]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >> 

(*
    The client leader creates a new ledger.
*)
CreateLedger(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = PENDING_CREATE_LEDGER
    /\ LET next_ledger == [id      |-> md_next_lid, 
                           open    |-> TRUE,
                           version |-> 0]
       IN /\ c_state' = [c_state EXCEPT ![c].ledger = next_ledger,
                                        ![c].status = PENDING_APPEND_LEDGER]
          /\ md_ledgers' = md_ledgers @@ (next_ledger.id :> next_ledger)
          /\ md_next_lid' = md_next_lid + 1
          /\ UNCHANGED << md_ll, md_ll_version, md_leader, written_ledgers >>

(*
    The client leader appends the new ledger to the ledger list. It uses the cached
    metadata from when it obtained the ledger list. The version in the metadata store has not
    changed so the update operation succeeds.
*)
AppendLedgerSuccess(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = PENDING_APPEND_LEDGER 
    /\ c_state[c].ll_version = md_ll_version
    /\ md_ll' = Append(md_ll, c_state[c].ledger.id)
    /\ md_ll_version' = md_ll_version + 1
    /\ c_state' = [c_state EXCEPT ![c].status = HAS_OPEN_LEDGER]
    /\ UNCHANGED << md_ledgers, md_leader, md_next_lid, written_ledgers >>

(*
    The client leader tries to append the new ledger to the ledger list. It uses the cached
    metadata from when it obtained the ledger list. But the version in the metadata store has 
    changed indicating that another client has also appended a ledger in the meantime.
    The client abdicates.
*)
AppendLedgerBadVersion(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = PENDING_APPEND_LEDGER 
    /\ c_state[c].ll_version < md_ll_version
    /\ c_state' = [c_state EXCEPT ![c].leader = FALSE,
                                  ![c].status = WAITING]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>

(*
    The client leader writes to the ledger. We don't actually bother modelling individual entries. We have
    already modelled that in the BookKeeperProtocol spec. We just want to track which ledgers
    got written to with this spec.
*)  
WriteToLedger(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = HAS_OPEN_LEDGER
    /\ c_state[c].ledger.id \notin written_ledgers
    /\ written_ledgers' = written_ledgers \union {c_state[c].ledger.id}
    /\ UNCHANGED << c_state, md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid >>
    
(*
    A client leader closes its own ledger and transitions to the PENDING_CREATE_LEDGER
    state so that it cannot chain a new ledger onto the list.
*)
CloseOwnLedgerSuccess(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = HAS_OPEN_LEDGER
    /\ LET ledger == c_state[c].ledger
       IN
            /\ ledger.id \in written_ledgers
            /\ ledger.version = md_ledgers[ledger.id].version
            /\ md_ledgers' = [md_ledgers EXCEPT ![ledger.id].open = FALSE,
                                                ![ledger.id].version = @ + 1]
            /\ c_state' = [c_state EXCEPT ![c].status = PENDING_CREATE_LEDGER]
    /\ UNCHANGED << md_ll, md_ll_version, md_leader, md_next_lid, written_ledgers >>

(*
    A client leader tries to close its own ledger but can't as ledger metadata was
    previously updated by a different client.
*)    
CloseOwnLedgerBadVersion(c) ==
    /\ c_state[c].leader = TRUE
    /\ c_state[c].status = HAS_OPEN_LEDGER
    /\ LET ledger == c_state[c].ledger
       IN
            /\ ledger.id \in written_ledgers
            /\ ledger.version < md_ledgers[ledger.id].version
            /\ c_state' = [c_state EXCEPT ![c].leader = FALSE,
                                          ![c].status = WAITING]
    /\ UNCHANGED << md_ll, md_ll_version, md_ledgers, md_leader, md_next_lid, written_ledgers >>
                                          
                                          
Next ==
    \E c \in Clients :
        \/ LeaderChosen(c)
        \/ BecomeLeader(c)
        \/ Abdicate(c)
        \/ GetLastLedger(c)
        \/ LedgerAlreadyClosed(c)
        \/ CloseLastLedgerSuccess(c)
        \/ CloseLastLedgerBadVersion(c)
        \/ CreateLedger(c)
        \/ AppendLedgerSuccess(c)
        \/ AppendLedgerBadVersion(c)
        \/ WriteToLedger(c)
        \/ CloseOwnLedgerSuccess(c)
        \/ CloseOwnLedgerBadVersion(c)

(* 
    Types 
*)

ClientStatuses == { 
          WAITING,
          GET_MD_FOR_CLOSING,
          CLOSE_LAST_LEDGER,
          PENDING_CREATE_LEDGER,
          PENDING_APPEND_LEDGER,
          HAS_OPEN_LEDGER }

Ledger == [id: Nat, open: BOOLEAN, version: Nat \union {-1}]

Client == [leader: BOOLEAN,
           status: ClientStatuses,
           ll_version: Nat \union {-1},
           ledger: Ledger]
          
TypeOK ==
    /\ c_state \in [Clients -> Client]
    /\ md_leader \in Clients
    /\ md_ll_version \in Nat
    /\ \/ md_next_lid = 1
       \/ /\ md_next_lid > 1
          /\ md_ledgers \in [1..(md_next_lid - 1) -> Ledger]
          /\ written_ledgers \in SUBSET (1..(md_next_lid - 1))
    /\ md_next_lid \in Nat

(*
    Invariant: No ledgers that were written to ended up outside
               of the ledger list.
*)
NoWrittenToLedgersLost ==
    IF written_ledgers # {}
    THEN     
        ~\E l \in 1..(md_next_lid - 1) :
           /\ l \in written_ledgers
           /\ \/ md_ll = <<>>
              \/ ~\E mdl \in DOMAIN md_ll : l = md_ll[mdl]
    ELSE TRUE
    
(* 
    Constraints
*)    

LedgerLimit == md_next_lid < 4
            
=============================================================================
\* Modification History
\* Last modified Thu Apr 01 14:16:08 CEST 2021 by jvanlightly
\* Created Thu Apr 01 12:05:02 CEST 2021 by jvanlightly
