{- | The terms of the automaton's accepting runs, each once.

Path equalities are solved by unification. Enumeration stops at a recursive
binder and reports it as the marker term @Mu@ rather than unfolding it;
bound the depth first with 'boundDepth' to see past it, or use 'plainTerms'
and 'plainTermsAtMost' for the depth-ordered listing of an automaton without
constraints. An acyclic automaton with no constraint anywhere is listed level
by level without the enumeration state. A constraint's residual beyond its equalities
is not decided here: use 'runs' to see it with the subterm it guards.

A constraint whose paths descend into a truncated recursive binder is dropped
rather than checked, so a result term containing the marker is not evidence
that the language below it is non-empty.
