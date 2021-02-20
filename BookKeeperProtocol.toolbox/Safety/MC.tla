---- MODULE MC ----
EXTENDS BookKeeperProtocol, TLC

\* CONSTANT definitions @modelParameterConstants:2AllowCrashDuringReplication
const_16081980394552000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:3AllowCrashDuringFencing
const_16081980394553000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:5SendLimit
const_16081980394554000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6AckQuorum
const_16081980394555000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:8RecoveryReadsFence
const_16081980394556000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:13AllowCrashDuringRecoveryReads
const_16081980394557000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:18WriteQuorum
const_16081980394558000 == 
3
----

=============================================================================
\* Modification History
\* Created Thu Dec 17 10:40:39 CET 2020 by jvanlightly
