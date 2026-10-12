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

## A finite leaf progress measure

`FiniteRowIntersection` proves termination for arbitrary Cartesian narrowing
of finite alternative sets when individual row conjunction is associative,
commutative, and idempotent. It retains the source self-intersection shortcut.
The operand can change after each pass. The proof does not require whole-set
absorption or decreasing edge counts.

The first measure is the number of rows in the upward closure of the
alternative set. Intersection can only remove closure members. If the
closure stays equal, every existing alternative remains. Each changing step
then adds an alternative. The lexicographic pair of closure count and missing
alternative count strictly decreases.

`SourceLeafRowProgress` derives the row algebra from the actual guard
normalizer and structural comparator. It generates the finite inventory
from all subsets of the original outer atoms. Its size is `2 ^ atomCount`
before duplicate removal. No supplied finite bound or absorption law is
required. `source_product_members` connects Cartesian source guard generation
to the finite product. The theorem covers canonical residual alternatives at
one leaf symbol. It does not include nested children, path edits, or the
separate equality field.

`FiniteLeafForestProgress` extends this result to complete forests of
canonical leaf alternatives at one symbol. Each equality path selects an
existing direct child. Each class reads all other projections from the same
old forest. The implementation uses the source's seeded right fold and
simultaneous coordinate updates. Complete schedules retain their right-fold
class order, empty-constraint shortcut, contradiction branch, and empty
propagation. The progress proof also allows overlapping selected classes.

For an inventory of length `N`, a leaf's natural potential is
`closureCount * (N + 1) + N - rowCount`. The forest potential is the sum
over its children. Every changed coordinate strictly decreases this value;
unchanged coordinates keep it. Thus every changing pass strictly decreases
the forest potential. `source_terminates` derives a fixed point within at
most the initial forest potential plus one passes. The finite guard inventory
and its size come from `SourceLeafRowProgress`, rather than a supplied bound.
This counts passes. It does not bound the cost of one source intersection.

The focused source probe `/tmp/mcfta-leaf-forest-progress.hs` checks 4,096
canonical three-child forests over three original guard atoms. It compares
each public pass with exact simultaneous source snapshot edits. It checks
the strict potential, empty propagation, and derived pass bound. All checks
pass; the largest case needs two changing passes. The probe uses the actual
canonical edge identities to identify rows. It is source evidence for this
fragment, not a proof of general nested reduction or physical cache identity.

`FiniteLeafSymbolsProgress` removes the single-symbol restriction. A node
has a separate alternative set for every symbol in a finite alphabet. The
self-intersection test still compares the whole node. If only one symbol's
rows agree, the source computes their Cartesian product unless the whole
nodes agree. The proof retains this distinction and derives progress for
each child-symbol coordinate. Summing those potentials gives the same
explicit pass bound for complete multi-symbol leaf forests. Empty means
that every symbol column is empty. A second source probe checks 4,096
two-symbol forests and their exact whole-node shortcuts; it passes.

`EqualityFixedPairs` proves a separate nested fragment: disjoint binary
classes at direct child roots stabilize after one changing pass. Node
intersection needs only commutativity and the self shortcut. It need not
be associative. A binary class below a projected union does not satisfy
that one-pass property. See [the fixed-pair notes](notes-equality-fixed-pairs.md)
for the source boundary example and exact schedule assumptions.

## Alternating nested operands can cycle

The source reproduction now also checks a stronger obstruction. Let `A`
have two leaf rows with distinct true guards. Let `B` have a third true guard.
Set `Z = intersect A B` and `W = intersect A Z`. Their row counts are two and
three. With `wrap X = Node [Edge "f" [X]]`, define:

```text
P = union [wrap W, wrap A]
R = union [wrap A, wrap B]
Q = wrap A
```

Then `intersect P R` differs from `P`, but
`intersect (intersect P R) Q == P`. The parent row counts are `2, 3, 2`.
Both changing steps preserve the singleton language and contain no binders
or free references. The original source identities return after two steps.

Thus no strict measure can cover every changing intersection with arbitrary
operands at all finite nesting depths. The leaf progress theorem cannot be
applied to child-node intersection as if it were associative conjunction.
This is not a counterexample to one fixed equality-reduction schedule: the
two operands differ. The source schedule must supply an additional invariant
that excludes these alternating transitions.

## Remaining proof obligation

A proof must bound the actual interned representations and exclude cycles
among distinct representations. A finite semantic universe establishes
neither property. A finite structural universe alone would establish only
eventual repetition. It would not establish the identity fixed point that
`fixUnbounded` requires.

The unresolved step is a strict progress relation for nested row sets under
path projection unions, simultaneous class edits, required-path filtering,
Cartesian intersection, and the closed self-intersection shortcut. No
cycle of the fixed source equality schedule has been established. The
arbitrary-operand cycle above excludes a schedule-independent measure. The guarded recursive case
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
