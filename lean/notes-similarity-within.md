# Classified similarity pair schedule

`SimilarityWithin.lean` models the `similarityWithin` optimization added on
`microcfta` in PR #90. The model follows
`microcfta/src/Data/CFTA/Refinement/Minimize.hs`.

The implementation first removes transitions whose classification is
`Nothing`. It groups each remaining transition by class. The map combine
function is `flip (<>)`, so each class queue retains source transition order.
It then traverses the classified input in its original order. At each entry,
it removes the head of that class queue and emits a pair with every remaining
member of the queue.

## Exact schedule

`group_acc` proves the map construction invariant from the actual append
operation. Every lookup returns the original class subsequence.
`later_invariant` proves that the source's unchecked head removal consumes
the current occurrence. The updated map contains exactly the queues for the
remaining input suffix. Duplicate input values do not break this invariant.

`scheduled_filtered` proves ordered list equality:

```
scheduled (classified classify items)
  = filter (eligible classify) (unorderedPairs items)
```

This proves that the optimization emits every eligible pair. It also proves
that it emits no other pair and does not reorder the pairs. A permutation or
a set equality would be too weak. The first unresolved subtyping query and
the deterministic choice of direction depend on this order.

`similarityWithin_exact` composes this equality with the existing
`MinimizeSchedule.inferPairs` model. The optimized and original inference
results are equal when the oracle returns `No` for every off-class pair.
The equality includes unresolved-direction errors and first-direction
preference. `similarityWithin_restricted` derives that condition from the
structural guard in the source `refinementSubtypingOn` adapter.

## Pair work

`scheduled_class_cost` proves the exact number of emitted candidate pairs:

```
sum over classes of n * (n - 1) / 2
```

Here `n` is the number of input occurrences in the class. The proof uses the
actual class queues and derives a complete distinct key list from the input.
It does not assume that values within a class are distinct. The source asks
one or two oracle questions for each processed candidate pair. It stops if a
pair has no known direction and has an unresolved possible direction.

The theorem counts candidate pairs. It does not prove the implementation
cost of `Data.Map`, classification, or the oracle. The finite map model uses
its lookup, insertion, and ordered combination laws. Runtime representation
and callback effects remain separate boundaries.

## Checked cases

Kernel examples cover interleaved classes, duplicate input values, excluded
transitions, and preservation of the first unresolved query. Interleaved
classes distinguish the source schedule from concatenating pair lists in
map-key order.

The result requires the documented class restriction. An arbitrary oracle
that returns `Yes` or `Unknown` across classes does not satisfy that contract.
Both source entry points perform the same validation before the modeled
schedule. The proofs do not add a new validation or solver assumption.
