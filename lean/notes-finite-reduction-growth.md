# Finite equality reduction and structural progress

`repro/FiniteReductionGrowth.hs` checks a finite acyclic example against the
public `reduceEqConstraints` operation and its explicit `fixUnbounded`
caller. The public operation now performs one pass, following PR #89.
The explicit repetition reaches a structural fixed point
after six changing rounds. This is a terminating example, not a new defect.
It excludes several proposed termination measures.

## The source witness

Both child domains contain one possible term: the complete binary tree with
three `f` levels and `a` leaves. The equality classes are
`{0.0, 1.1}` and `{0.1, 1.0}`. Every required path exists. No node contains a
binder or a free reference.

The alternative rows use these residual guards:

- `Top`;
- `Same [] []`;
- `Or [Same [] []]`;
- `Not Bottom`.

Each guard is true on every term in this example. The source retains their
different structural representations. Intersection combines the outer
conjuncts, but does not remove semantically redundant alternative rows.

The fixture checks that every row has the expected term shape, that each
child accepts the expected term, and that each child has zero nested binders
and no free references after every pass. These checks establish the singleton
language for this fixture. They do not depend on enumerating duplicate
derivations.

The observed values of `edgeCount` and `nodeCount` are:

| Changing rounds | Child 0 edges | Child 1 edges | Child 0 nodes | Child 1 nodes |
| --- | ---: | ---: | ---: | ---: |
| 0 | 16 | 12 | 12 | 11 |
| 1 | 28 | 29 | 19 | 20 |
| 2 | 28 | 55 | 19 | 28 |
| 3 | 76 | 81 | 32 | 33 |
| 4 | 76 | 90 | 32 | 34 |
| 5 | 86 | 91 | 33 | 34 |
| 6 | 86 | 92 | 33 | 34 |

The next pass returns the same node identities. The fixture separately
checks the public single pass against the instrumented pass. It then forces
the explicit public fixed-point iteration, compares it with the instrumented
schedule, and checks its stability.

The instrumented pass follows the source class order and computes all class
projections from the same input forest. It then applies the path-local
intersections. The two paths of each class have no prefix overlap, so these
edits commute. `requireAll` has no effect on this fixture because all selected
paths exist. The recursion gate and empty propagation also have no effect.

## Failed proof shortcuts

The same fixture contains a smaller check of structural absorption. Let
`A` contain two `a` rows, guarded by `Same [] []` and `Or [Same [] []]`.
Let `B` contain one `a` row, guarded by `Not Bottom`. Then:

```text
nodeEdges (intersect A B)                  has length 2
nodeEdges (intersect A (intersect A B))    has length 3
```

The extra row contains all three conjuncts. Thus structural intersection
does not satisfy `A intersect (A intersect B) = A intersect B`. Canonical
guard conjunction alone does not establish a lattice law for whole nodes.
The source also returns a closed node unchanged on self-intersection. That
shortcut must remain in any structural model of the operation.

The nested example keeps the accepted term set and its depth unchanged
during six strict identity changes. Its edge and node counts increase.
Language inclusion, language cardinality, term depth, node count, and edge
count therefore do not supply a strict decreasing measure for this loop.
The existing two-pass theorem for three single-row leaf residuals does not
extend to these nested alternative domains.

## Remaining proof obligation

A proof must bound the actual interned representations and exclude cycles
among distinct representations. A finite semantic universe establishes
neither property. A finite structural universe alone would establish only
eventual repetition. It would not establish the identity fixed point that
`fixUnbounded` requires.

The unresolved step is a strict progress relation for nested row sets under
path projection unions, simultaneous class edits, required-path filtering,
Cartesian intersection, and the closed self-intersection shortcut. No
general measure or cycle has been established. The guarded recursive case
and completed-execution preservation theorems remain separate results.

`EqualityTermination.mkEqConstraints_terminates` proves termination of
equality-class normalization. It does not cover node reduction.
`RecursiveReductionSourceOrder.terminates_two` proves the two-pass bound for
three single-row leaf residuals under the source guard order. It does not
cover alternative rows or nested paths. `RecursiveReductionBarrier` proves
the finite path inspection used to skip recursive domains. It does not
establish progress for the eligible acyclic domains.

`EqualityReduction.constrained_reduce_exact` and the
`PartialReductionCaller` theorems establish preservation for completed
executions. Their primitive source adapters and the existence of a sufficient
execution bound remain separate obligations. The pruning caller still uses an
unbounded identity fixed point for eligible classes. `reduceEqConstraints`
and each local edge of `reducePartially` now perform one pass. Repeated outer
calls to `reducePartially` require a separate termination argument as well.

## Validation

The witness passed in the repository Nix environment on 2026-10-12. It was
formatted with `fourmolu`. Run it against the local build with:

```sh
nix-shell --run 'cabal exec -- runghc -package=microcfta lean/repro/FiniteReductionGrowth.hs'
```

The diagnostic limits its copied schedule to twelve rounds and gives the
public call five seconds. These are diagnostic limits. The explicit source fixed-point operation
has no such limit.
