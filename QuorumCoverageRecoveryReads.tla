--------------------------- MODULE QuorumCoverageRecoveryReads ---------------------------
EXTENDS QuorumCoverage, Naturals, FiniteSets, Sequences, Integers, TLC

(*
    Mostly an intellectual exercise, but should definitively answer the
    question what quorum coverage means.

    Demonstrates the equivalence of the different ways of
    determining quorum coverage, in the context of the recovery reads of a single entry.
    
    The second phase of ledger recovery is recovery reading and writing. Reading completes
    when it gets enough negative read responses for an entry such that there can exist
    no ack quorum of bookies that might have the entry.
    
    In terms of quorum coverage, the cohort is the writeset of the entry. The writeset
    is the ensemble of bookies that should host that entry. When the ensemble size >
    write quorum, entries are striped across bookies. Each entry is stored on a deterministic
    subset of the current ensemble, this is the writeset.
    
    Current ensemble /= Writeset where E > WQ.
*)

CONSTANT ALL_BOOKIES    \* the bookies to use e.g. {b1, b2, b3, b4, b5}. 
                        \* All permutations will be tested.
         
\* Model values for responses         
CONSTANT PENDING,           \* pending a response
         OK,                \* positive read result
         NO_SUCH_ENTRY,     \* negative read result
         UNKNOWN            \* unknown (time out or error response)
         
VARIABLE curr_ensemble, \* the current ledger ensemble (size E)
         write_set,     \* the ensemble of the given entry being read (size WQ)
         wq,            \* the write quorum
         aq,            \* the ack quorum
         state          \* the state of the read sent to each bookie (pending, OK, NoSuchEntry etc)

ReadResponses == { OK, NO_SUCH_ENTRY, UNKNOWN }
AllResponses == ReadResponses \union {PENDING}    

\* Produces every permuation of ensemble, writeset, WQ and AQ possible given
\* the pool of bookies (ALL_BOOKIES)
Init ==
    \E ensemble \in SUBSET ALL_BOOKIES :
        \E write_quorum \in 1..Cardinality(ensemble) :
            /\ \E writeset \in SUBSET ensemble :
                /\ Cardinality(writeset) = write_quorum
                /\ \E ack_quorum \in 1..write_quorum :
                    /\ curr_ensemble = ensemble
                    /\ write_set = writeset
                    /\ wq = write_quorum
                    /\ aq = ack_quorum
                    /\ state = [b \in ensemble |-> PENDING]   
            
\* Receive recovery read responses from each bookie until all responses received 
Next ==
    \E b \in curr_ensemble :
        \E res \in ReadResponses : 
            /\ state[b] = PENDING
            /\ state' = [state EXCEPT ![b] = res]
            /\ UNCHANGED << curr_ensemble, write_set, wq, aq >>            

\* 4 ways of deciding if the responses so far reach the quorum coverage
\* threshold for the entry being treated as unrecoverable   
ReadIsNegative1 ==
    HasQuorumCoverageUsingAffirmative(
        { b \in write_set : SatisifiesProp(state, b, NO_SUCH_ENTRY)}, wq, aq)

ReadIsNegative2 ==
    HasQuorumCoverageUsingAffirmative2(
        { b \in write_set : SatisifiesProp(state, b, NO_SUCH_ENTRY)}, 
        write_set, aq)
    
ReadIsNegative3 ==
    HasQuorumCoverageUsingNonAffirmative(
        { b \in write_set : NotSatisifiesProp(state, b, NO_SUCH_ENTRY, AllResponses)}, aq)

ReadIsNegative4 ==
    HasQuorumCoverageUsingNonAffirmative2(
        { b \in write_set : NotSatisifiesProp(state, b, NO_SUCH_ENTRY, AllResponses)}, 
        write_set, aq)
                    
\* An invariant for the equivalence of each method
Equivalence ==
   /\ ReadIsNegative1 <=> ReadIsNegative2
   /\ ReadIsNegative1 <=> ReadIsNegative3
   /\ ReadIsNegative1 <=> ReadIsNegative4 

=============================================================================
\* Modification History
\* Last modified Wed Nov 24 18:19:53 CET 2021 by GUNMETAL
\* Created Wed Nov 24 12:03:06 CET 2021 by GUNMETAL