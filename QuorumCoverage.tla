------------------------- MODULE QuorumCoverage -------------------------
EXTENDS Naturals, FiniteSets, Sequences, Integers, TLC

(*
    4 alternative ways of measuring quorum coverage.
    
    The cohort changes according to what property is being measured:
        - fencing cohort = current ensemble
        - recovery read cohort = entry writeset
        
    The 4 methods can be classified as either:
    - measuring the set of bookies that satisfy a property (1st and 2nd)
    - measuring the set of bookies that do not satisfy a property (3rd and 4th)        
*)

HasQuorumCoverageUsingAffirmative(satisifies_prop, cohort_size, aq) ==
    Cardinality(satisifies_prop) >= (cohort_size - aq) + 1
    
HasQuorumCoverageUsingAffirmative2(satisifies_prop, cohort, aq) ==
    /\ satisifies_prop # {}
    /\ \A ack_quorum \in { s \in SUBSET cohort : Cardinality(s) = aq } :
        satisifies_prop \intersect ack_quorum /= {}   

HasQuorumCoverageUsingNonAffirmative(not_satifies_prop, aq) ==
    /\ Cardinality(not_satifies_prop) < aq
    
HasQuorumCoverageUsingNonAffirmative2(not_satifies_prop, cohort, aq) ==
    ~\E ack_quorum \in { s1 \in SUBSET cohort : Cardinality(s1) = aq } :
        ack_quorum \intersect not_satifies_prop = ack_quorum

SatisifiesProp(state, b, target_response) ==
    state[b] = target_response

NotSatisifiesProp(state, b, target_response, responses) ==
    state[b] \in (responses \ {target_response})

=============================================================================
\* Modification History
\* Last modified Wed Nov 24 18:14:05 CET 2021 by GUNMETAL
\* Created Wed Nov 24 15:29:13 CET 2021 by GUNMETAL
