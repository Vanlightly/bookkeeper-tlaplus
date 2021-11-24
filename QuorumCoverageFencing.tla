--------------------------- MODULE QuorumCoverageFencing ---------------------------
EXTENDS QuorumCoverage, Naturals, FiniteSets, Sequences, Integers, TLC

(*
    Mostly an intellectual exercise, but should definitively answer the
    question what quorum coverage means. 

    Demonstrates the equivalence of the different ways of
    determining quorum coverage, in the context of the fencing of a ledger.
    
    The first phase of ledger recovery is fencing and completes when
    enough bookies of the current ensemble are fenced. There can exist no Ack Quorum
    of bookies of the current ensemble that might remain unfenced.
    
    In terms of quorum coverage, the cohort is the current ensemble.
    
    For each bookie the client either knows it is fenced or doesn't know either way
    due to having not received a response yet, getting an error response or timeout.
*)

CONSTANT ALL_BOOKIES    \* the bookies to use e.g. {b1, b2, b3, b4, b5}. 
                        \* All permutations will be tested.
         
\* Model values for responses         
CONSTANT PENDING,       \* pending a response
         FENCED,        \* bookie is fenced 
         UNKNOWN        \* unknown (timeout or error response)
         
VARIABLE ensemble_size, \* the ensemble size, E
         curr_ensemble, \* the current ledger ensemble (size E)
         aq,		    \* the ack quorum
         state		    \* the state of the fence request sent to each bookie (pending, fenced etc)
    
FencingResponses == { FENCED, UNKNOWN }
AllResponses == FencingResponses \union {PENDING}

\* Produces every permuation of ensemble and AQ possible given
\* the pool of bookies (ALL_BOOKIES) 
Init ==
    \E ensemble \in SUBSET ALL_BOOKIES :
        /\ \E ack_quorum \in 1..Cardinality(ensemble) :
            /\ ensemble_size = Cardinality(ensemble)
            /\ curr_ensemble = ensemble
            /\ aq = ack_quorum
            /\ state = [b \in ensemble |-> PENDING]

\* Receive fence responses from each bookie until all responses received                
Next ==
    \E b \in curr_ensemble :
        \E res \in FencingResponses : 
            /\ state[b] = PENDING
            /\ state' = [state EXCEPT ![b] = res]
            /\ UNCHANGED << ensemble_size, curr_ensemble, aq >>

\* 4 ways of deciding if the responses so far reach the quorum coverage
\* threshold to allow recovery to move to the recovery read phase            
EnoughFenced1 ==
    HasQuorumCoverageUsingAffirmative(
        { b \in curr_ensemble : SatisifiesProp(state, b, FENCED)}, ensemble_size, aq)

EnoughFenced2 ==
    HasQuorumCoverageUsingAffirmative2(
        { b \in curr_ensemble : SatisifiesProp(state, b, FENCED)}, 
        curr_ensemble, aq)
    
EnoughFenced3 ==
    HasQuorumCoverageUsingNonAffirmative(
            { b \in curr_ensemble : NotSatisifiesProp(state, b, FENCED, AllResponses)}, aq)

EnoughFenced4 ==
    HasQuorumCoverageUsingNonAffirmative2(
            { b \in curr_ensemble : NotSatisifiesProp(state, b, FENCED, AllResponses)},
            curr_ensemble, aq)            

\* An invariant for the equivalence of each method
Equivalence ==
   /\ EnoughFenced1 <=> EnoughFenced2
   /\ EnoughFenced1 <=> EnoughFenced3
   /\ EnoughFenced1 <=> EnoughFenced4

=============================================================================
\* Modification History
\* Last modified Wed Nov 24 18:19:10 CET 2021 by GUNMETAL
\* Created Wed Nov 24 12:03:06 CET 2021 by GUNMETAL