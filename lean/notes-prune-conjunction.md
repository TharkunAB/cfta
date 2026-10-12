# Residual conjunction growth during equality pruning

An acyclic automaton can make the old equality-narrowing fixpoint diverge.
The root has three `a` leaves and the equality class `[0] = [1] = [2]`.
The leaf guards are `Same [] []`, `And [Same [] [], Same [] []]`, and
`Or [Same [] [], Same [] []]`. All three guards accept the same leaf.
Validation succeeds. The complete `triple(a,a,a)` term is accepted.

Each narrowing pass intersects one child with both other children.
The old `combineGuards` removed `Top` and identical operands only.
It retained nested conjunctions with different syntax. The three residual
guards had sizes 9, 29, 89, and 269 after successive passes. Their interned
identities stayed different. The pruning fixpoint did not finish.

`PruneTerminationGrowth.lean` models this guard fragment and the old function.
It permits either operand order at all six intersections in each pass.
`first_with_distinct` proves that every initial ordering produces three
different guards of size 9. `round_growth` proves that every later ordering
preserves distinctness and changes size `w` to `3 * w + 2`.
`round_all_old` connects all six intersections to the old conjunction shortcuts.
`runs_width` proves `w + 1 = 10 * 3^n` after `n` additional rounds.
`round_not_fixed` proves that another round cannot reach the previous state.
`every_guard_accepts` proves that every generated guard still accepts the leaf.

The repair flattens outer `And` constructors, removes `Top`, and sorts and
deduplicates the resulting conjuncts. It does not cross a `Not`, `Or`, or
`Substitute` constructor. It leaves the equality-narrowing algorithm unchanged.
Replacing every constrained position by one common intersection is unsound.
That replacement can lose the correlation between an outer constructor and
its child. The existing pruning suite now checks both convergence and a
nested `f(a) | g(b)` case that rejects crossed children.

`repro/PruneConjunction.hs` runs the source example. After the repair, all
three residual guards have size 5 after the first pass. Further passes reuse
the same interned node. Pruning finishes and retains the accepted term.
The pruning suite also checks that a second complete prune returns the same
automaton.

This result removes this source divergence. It does not prove termination of
every equality-narrowing fixpoint or every recursive pruning computation.
The guard proof and the source regression are separate from that remaining
termination obligation.
