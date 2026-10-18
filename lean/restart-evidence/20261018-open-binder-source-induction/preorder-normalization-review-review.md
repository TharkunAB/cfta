# Actual canonical normalization and directional simulation

Date: 2026-10-18 13:15 CEST.

## Checked integration

The selected printer-free source is
`preorder-normalization-review-kernels-5.source.lean`, SHA-256
`e3ddfcd05d9366320671241d81b626ec5c7a3e3947e2c36a1d2e43903c8db027`.
The one public constructed theorem is
`MicroCFTA.PreorderNormalizationReview.witness`.

The fixture executes this closed source from the empty physical heap:

```
binder false (node [9 false
  [union [binder false (leaf 1), binder false (leaf 2), var 0],
   union [union [leaf 1, leaf 2], var 0]]])
```

Each leaf is an ordinary nullary row with the stated symbol and false full
guard. The outer stored body contains both tested values. Its interned
self reference is the bare alternative `z`. Both inner binders use the raw
`false` flag, so their unused local variables do not erase their literal
Mu records. Their actual stored bodies are the distinct ordinary nodes
`A` and `B`.

The literal source build derives `Ready reader`. The actual returned
payload derives availability of both tested values in that same reader.
The witness retains these exact warm constructor pairs:

```
makeUnion [MuA, MuB, z] = (u, reader)
makeUnion [A, B]       = (merged, reader)
makeUnion [merged, z]  = (v, reader)
```

It also retains both literal warm Mu unfolds to `A` and `B`.
Both `u` and `v` are actual canonical results. No manually constructed
union record or modified observation reader is used.

## Exact grouping correction

The initial proposed flat schedule `makeUnion [A,B,z]` does not produce
`v`. The ordinary fast path requires every member to be an ordinary node.
The bare reference `z` makes `ordinaryEdges` return `none`. The actual flat
schedule retains the separate ordinary members `[A,B,z]`.
The first failed snapshot records this source-backed correction. The
selected theorem states the grouped schedule explicitly. It does not
claim flat and grouped physical results are equal.

## Observations and the old obstruction

The proof classifies every actual epsilon-reachable value:

* From `u`: exactly `u`, `MuA`, `MuB`, `z`, `A`, and `B`.
* From `v`: exactly `v`, `merged`, and `z`.

The reference origin on either side is exactly `z`'s name. The row origins
are exactly the original `A` and `B` rows. Full fields and child order are
retained. These exact origins derive `Same depth reader [u] [v]` for every
finite depth.

The old `Forward` path theorem sends the actual two-step path
`u -> MuA -> A` to a related value reachable from `v`. If both old global
Forward laws held, their `same` theorem would give `Same 1` between `A`
and that reached value. All three possible values fail:

* `v` and `z` expose a bare reference; `A` exposes none.
* `merged` exposes the `B` row; `A` has only its symbol-1 row.

The checked conclusion excludes every binary relation that contains
`(u,v)` and satisfies both old Forward laws. This does not refute the old
conditional theorem. It refutes its use as a necessary general matching
interface for these actual normalized outputs.

## Positive directional instance

The same witness constructs a relation for the new `Directed` interface.
The finite support helper was supplied by the independent simulation owner
and is copied privately into this checked source. Its supports are the
exact reachable sets above. Literal successor closure, bare references,
and physical row origins derive every local clause. The relation is
identity plus each left support value paired with `v` and each right
support value paired with `u`. Ordered row children match by identity and
therefore retain mutual relation membership.

The witness concludes that this relation is `Directed reader` and relates
`u` and `v` mutually. It does not use `Same` as a premise. The relation is
not asserted to be transitive. The new interface does not require that
additional property. No source-wide or retained-binder simulation instance
is claimed.

## Validation and preservation

`preorder-normalization-review-kernels-5` exits zero and has an actual
zero-byte log. `preorder-normalization-review-public-1` prints the exact
public theorem type, full proof, and axiom report. All eight options are
explicit. The output has no omission, printer failure, warning, error, or
`sorryAx`. Its axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
This component contributes one constructed pair, no public production pair,
and no auxiliary pair.

Selected checks use pinned Lean 4.34.1, a five-minute cap, and inner
readback of effective memory limits 4294967296/4294967296/0. The highest
selected peak is 759 MiB. The highest peak across all preserved attempts
is 783 MiB.

All failed snapshots remain present. Attempt 1 includes the false flat
merging assertion, an edge-key constructor field-order error, and direct
membership goals. Attempt 2 checks the corrected grouped calls. Attempt 3
checks the all-depth observations and old obstruction. Attempt 4 has only
list-membership simplification errors in the new positive support proof.
Attempt 5 checks the final negative and positive witness. No production
source or older frozen component was changed.

No Haskell execution defect, general recursive termination result, or
retained used-Mu alignment follows from this finite canonical fixture.
