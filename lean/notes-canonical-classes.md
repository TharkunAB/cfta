# Canonical ordered partition refinement

`MicroCFTA/CanonicalClasses.lean` models `canonicalClasses` in
`microcfta-generator/src/Data/CFTA/Gen/Internal/Automaton.hs`.
This is the graph class routine used by ordinary automaton row ordering and
compact import ordering. It is separate from `SymbolicCanonicalOrder`, which
orders operands of an intersection.

## Exact source operations

`Graph` has a finite duplicate-free node list, a complete identity domain, and
outgoing edge rows. Each edge has an ordered key and an ordered child list.
All children belong to the domain by construction. This is the condition that
makes the source `IntMap.!` class lookups defined.

`nodeKey` contains the old numeric class first. Its second field is the sorted
list of edge keys paired with their ordered child classes. Sorting retains
repeated edge rows. `keys` removes duplicate complete node keys and sorts them.
`step` assigns each key its zero-based index in that sorted list. These are the
source `sort`, `Set.toAscList`, and ascending `Map` numbering operations.

The formal model uses natural class numbers. Source `Int` representation limits
and the implementation of `IntMap`, `Map`, and `Set` are outside this model.
Ordered keys have the usual source order laws. Renaming and canonical set
readback require a transitive comparison whose equality agrees with structural
equality. No language-equivalence or desired-partition premise is supplied.

## Termination and the stopping test

`step_equal_iff` proves that nodes receive the same new number exactly when
their complete source keys agree. `no_merge` then follows from the old class
at the start of each key.

`Dense` states that class numbers are exactly `0 .. count - 1`. The source
initial table satisfies it, including the empty graph. Every `step` also
satisfies it. Every old class occurs in a new key, so `count_monotone` proves
that the count cannot decrease. `count_bound` bounds every new count by the
number of nodes. `count_progress` proves strict increase in every round that
does not stop.

`refine` is the source loop with an explicit proof budget. Its only stopping
condition is equality of the old and new distinct-key counts. A failed budget
returns `none`; the termination theorem proves that this case cannot occur
with the supplied canonical budget. `refine_terminates` needs at most one plus
the number of remaining possible class splits. `canonical_terminates` proves
that every finite closed graph completes.

`count_equal_partition` proves that the source equal-count test means that no
class split. `stopped_projection` proves that, in this case, the old class
components of the new sorted keys are exactly the ascending class-number
range. `count_equal_fixed` therefore proves the stronger fact that the next
numeric table equals the old table. `canonical_fixed` proves that every
completed result is an exact numeric fixed point.

## Identity and ordering invariants

`step_preserves_order` proves that every existing strict class order survives
a round. `refine_preserves_order` extends it through the executed loop.
`no_merge_after_refine` proves that later rounds cannot reverse an earlier
separation by merging the nodes.

`Renaming` gives forward and backward identity maps. It requires exact edge
keys and ordered child references. It permits both node enumeration changes
and edge-row permutations. `nodeKey_rename` proves equality of the actual
sorted source keys. `keys_rename`, `step_rename`, and `refine_rename` then prove
that every numeric operation commutes with renaming. `canonical_rename` proves
that the final numeric class table changes only its identity lookup.

`final_edge_key_rename` and `final_sorted_rows_rename` expose the ordering
consequences used by the compact path. They cover keys of the form
`(arity, symbolOrderKey)` by choosing that pair as the edge key type.
`final_rows_exact` proves that equal final classes have identical sorted edge
keys and child-class rows.

These statements concern class and edge keys. They do not assert that equal
classes denote equal constrained languages. The source class key omits edge
constraints and can use a noninjective symbol order key. They also do not
assert a unique ordering of distinct transition payloads with equal final
keys. The source stable `sortOn` tie behavior needs a separate argument when
such ties are possible.

## Checked examples and validation

The delayed-split example starts with three nodes in one class. The first
round separates a leaf from two unary rows. The second round separates those
two rows through their child classes. A third round confirms the fixed point.
The example checks that two rounds are insufficient and that the complete
loop returns classes `[0, 1, 2]`.

The cyclic example includes a self reference. A structural identity swap and
reversed domain enumeration produce the same content-based numbers at the
renamed nodes. The empty example stops at zero classes.

Lean 4.34.1 checks all proofs and the concrete examples. The command
`lake -d lean build MicroCFTA.CanonicalClasses` passes. No Haskell file changed,
and no Cabal build ran for this module. Validation date: 2026-10-12.
