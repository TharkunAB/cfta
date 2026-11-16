# Why free monotonicity alone is insufficient

For an entered key, extend constructs its free names from sortedSet(newBound ++ names(parent)). Equality with the new original U/P key therefore bounds every old free name by uid. It does not distinguish an absent uid binding from one already present before the enter. This is an algebraic loss of information, not a claimed reachable source state or a runtime counterexample.

Selected Mu freshness plus singleton seen identifies parent.seen=[] but does not alone relate that seen set to free. The actual compiler control proof supplies precisely that missing relationship. No fabricated cache is used as an execution witness.
