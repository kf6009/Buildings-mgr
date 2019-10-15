---- MODULE MC ----
EXTENDS Buildings, TLC

\* CONSTANT definitions @modelParameterConstants:0Buildings
const_157108157273248000 == 
{"b1", "b2", "b3"}
----

\* CONSTANT definitions @modelParameterConstants:1People
const_157108157273249000 == 
{"p1", "p2", "p3"}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157108157273351000 ==
\A p \in DOMAIN location : location[p] \in permission[p]\union{Outside}
----
=============================================================================
\* Modification History
\* Created Mon Oct 14 20:32:52 BST 2019 by alun
