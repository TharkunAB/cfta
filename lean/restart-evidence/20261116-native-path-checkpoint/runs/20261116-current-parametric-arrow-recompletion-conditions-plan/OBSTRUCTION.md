# A generic obstruction to using isolation alone

This is an algebraic candidate, not a checked Lean counterexample or an accepted-source execution.

Let A be an isolated pending representative with actual native U and no current suspended constraints. Let B store the expanded type fragment arrow(hole A,var1). Use independent UF roots and levels B=0,A=1, frontier1. There are no current incoming suspended references to A. The state is structurally stratified, and a finite choice at A gives a finite current model and TypeIn value at B.

Suppose an EARLIER removed bucket at A required A.[1]=B. Restoring it while retaining B's current stored equation requires A.child1=B and B.child1=A. No finite terms satisfy this proper cycle. Same-position congruence is vacuous for this single occurrence. Thus current isolation, stratification, finite target values and same-position aliases alone do not suffice.

A genuine source suffix should exclude the new B fragment because the actual returned fragment must avoid the previously isolated A class. That is the proposed operational producer; the handcrafted core does not supply such a trace. No Haskell/source defect is claimed.

The earlier three-path caution also remains: A.[1]=B,A.[1]=C,B.[1]=C has an acyclic direct path graph, but congruence B=C creates a proper cycle. Neither observation permits replacing the full joint goal with independent witnesses or a direct path DAG test.
