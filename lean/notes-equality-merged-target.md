# Repeated ordinary target merging

Checkpoint: 2026-10-13. Source base: `origin/microcfta` at `9508eb3`.

## Result

`EqualityMergedTargetFixedPoint.fixed_point_complete` proves a finite bound
for repeated `mergeAlternatives` on finite ordinary trees. Start with
`Facts`, `Prepared`, and an available input. After at most the input's
ordinary height of completed calls, the next call returns the same
complete value and the same cache. This last call succeeds at every
comparison fuel. `Runs` retains the actual returned cache between calls.

The final theorem has no recursive callback, finite-universe, root-shape,
or constructor-readback premise. Earlier constructor proofs derive cache
facts from source syntax. This theorem accepts those facts directly. It
does not replace the actual runtime cache with a prepared observation.

The fragment permits `EmptyNode` and nested ordinary nodes. It excludes
references, Mu records, and explicit union records anywhere in the tree.
The source worker leaves open ordinary roots unchanged. The theorem does
not require every ordinary node to start in canonical readback form.

## Source policy obstruction

One target merge is not necessarily idempotent. Build a child with five
distinct guard rows. Build five parent rows with distinct guards and the
same child. The first merge replaces the parent group with one Top edge.
Its retained child column has one distinct value, so the singleton branch
returns that original child unchanged. The second merge takes the small
parent-group branch and then merges the child. The third merge is fixed.

`EqualityMergedTargetDelay.lean` executes the actual cold worker and
constructor caches. It proves the original source cache facts,
preparation, availability, closedness, ordinary height two, both changing
root identities, the row shapes, and the final repeated identity. These
are kernel computations. They do not use `native_decide`.

The native Haskell fixture gives the same observations:

```text
("shapes",[(5,[5,5,5,5,5]),(1,[5]),(1,[1]),(1,[1])])
("second-changes",True)
("third-fixed",True)
```

The source fixture uses these ordinary constructors:

```haskell
let guards = [semanticConstraint (Not (Or (replicate count Top))) | count <- [1 .. 5]]
    child = Node [mkEdge "a" [] guard | guard <- guards] :: Node String
    original = Node [mkEdge "f" [child] guard | guard <- guards]
    first = mergeAlternatives original
    second = mergeAlternatives first
    third = mergeAlternatives second
```

The fixture is `/tmp/mcfta-merged-target-delay.hs`. Its native Nix build
and execution log is `/tmp/mcfta-merged-target-delay.log`. The Lean
counterexample is the durable checked record. This behavior follows the
current singleton policy. It is not a source defect or a complete equality
schedule cycle.

## Proof structure

- `EqualityMergedTargetLayers` proves the structural layer argument. A
  completed pass adds one normalized layer. Child height decreases.
- `EqualityMergedTargetShape` follows actual successful child maps. Small
  roots retain the original child behind each returned recursive result.
  Canonical node normalization can discard rows but cannot invent children.
- `EqualityMergedTargetHeight` derives preservation of the finite ordinary
  fragment and height nonincrease. It includes actual stateful selection,
  the singleton branch, ordinary union, and constructor readback.
- `EqualityMergedTargetNormalization` combines those results with the
  actual complete symbol/arity root bound. Original height bounds recursive
  group-count normalization. It also derives runtime trace completion.
- `EqualityMergedTargetReadback` reuses
  `MergedNormalReadback.normal_transfer`. One verified immutable readback
  transfers to any coherent cache that retains the same complete value.
  The full proof is shared, not duplicated.
- `EqualityMergedTargetFixedPoint` strengthens each normalized layer with
  exact constructor replay. A recursively exact value then returns the
  same value and cache. Runtime completion and the layer bound give the
  final theorem.

`MergedColdMergeRootBounds` supplies the complete source root bound and
the exact final `makeNode` replay. `MergedColdMergeMapFacts` supplies actual
ordered callback facts. The proofs keep guard fields, group threshold
four, child positions, structural grouping, and canonical row filtering.

## Validation

The pinned Lean 4.34.1 build passed for
`MicroCFTA.EqualityMergedTargetFixedPoint` and
`MicroCFTA.EqualityMergedTargetDelay`. The final combined build contains
373 dependency jobs. The focused audit checks all 59 new theorem
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
There are no admitted obligations, custom axioms, or native decisions.

Audit input: `/tmp/mcfta-equality-target-axioms-20261013.lean`.
Audit log: `/tmp/mcfta-equality-target-axioms-20261013.log`.

A bounded local immutable-row search also examined 68,647 merged-target
equality cases. Of those cases, 68,645 reached a fixed point and two
exceeded the size cutoff. It found no cycle and observed up to seven
passes. This search is model exploration, not a proof or a source replay.
The script and log are `/tmp/mcfta-merged-nested-search.py` and
`/tmp/mcfta-merged-nested-search.log`.

## Remaining boundary

General equality fixed-point termination remains open. The live source
schedule merges peer targets, intersects them with a first-seeded fold,
and edits multiple endpoints. Those intersections and edits can change
the rows supplied to the next merge. The target-only theorem does not
bound that complete schedule.

The next useful obligation is a source-derived progress measure for a
fixed nested endpoint schedule that includes these merged target changes.
Do not assume one-pass target idempotence. Do not reuse an arbitrary
finite-universe premise as if it followed from source execution. Earlier
unmerged saturation and degree counterexamples remain distinct from the
current merged-target policy.

For Mu or explicit union inputs, ordinary height ignores their contents.
Extending the height theorem through union flattening needs a derived
source union-normal-form invariant or a different measure. The current
ordinary-tree theorem makes this boundary explicit.
