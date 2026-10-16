# Current inherited-child continuation: next target

Read-only review at 2026-10-16 09:57 CEST. No proof source, Haskell source,
Audit, documentation, or Git state was changed. No build was run for this
review. The file records a proposed next proof, not an existing endpoint.

## Actual source order

`cfta/src/Data/CFTA/Equality/Operations.hs:76–96` first memoizes
`reducePartially' inherited node`. An ordinary node maps
`reduceChildren inherited . reduceEdgeIntersection inherited` over its rows.
The child continuation therefore receives the RETURNED edge. It does not
receive the original edge or the original child list.

For a returned edge `edge`, lines 93–96 compute

```
setChildren edge
  (reduceWithInheritedEcs
    (combineEqConstraints inherited (equalities (edgeConstraint edge)))
    (edgeChildren edge))
```

The combination has inherited constraints FIRST and the returned own
accessor SECOND. The source shares this combined argument across the child
walk. Do not implement the walk by calling
`SourceEqualityPartialPayloadAllocation.childInheritance` once per child:
that function includes a combination and would repeat that operation.

Lines 143–145 give the two child branches. Contradiction maps every
existing child to `EmptyNode`. It makes no descent or recursive child call.
A live payload uses zero-based positions and calls
`reducePartially' (eqConstraintsDescend combined index) child` for each
existing child. Live empty constraints still invoke the recursive worker
for every child. An empty child list makes zero recursive calls.

`Equality/Constraint.hs:449–460` adds a demand short circuit:
`combineEqConstraints EqContradiction _` does not demand its second
argument. Thus an inherited-contradiction child continuation need not load
or execute the returned own accessor. A faithful prefix should expose
this branch separately. An available returned field may still be derived
as a logical invariant; that proof does not establish an accessor call.
Other branches can demand that accessor. The completed serial model must
label its chosen order and retain the GHC demand boundary.

## Minimal finite allocation prefix

Use the current full checked state `SourceEqualityNativeDemand.State width`.
Its operation state is `SourceEqualityConstraintMemoAllocation.State`.
Use the literal heap-preserving update

```
advancePhysical before <before.native.machine.heap, returnedOperations>
```

from `SourceCurrentAllocatedQueryMemo`. This retains the whole native
state definitionally when only operations change. In particular, neither
native memo family nor the domain cache is reset.

A small new `Prefix` graph or executable pair can have these branches:

1. Inherited contradiction: return contradiction and the exact initial
   checked state. No own-accessor, combination-cache, or descent event.
2. Live inherited value: read the returned raw edge constraint with
   `SourceCurrentConjunctionEquality.accessor`, then run the literal
   `SourceEqualityConstraintMemoAllocation.combine inherited own` at its
   returned operation state. Retain both returned states and any explicit
   error or missing-field observation.

Inputs are initial `SourceCurrentConjunctionClassScan.Ready before`,
`InventoryState.At formulas solver inventory before`, returned-edge
residency, and `ConstraintAllocation.Ready before.operations.constraints
inherited`. The current `Ready.good.fields` derives the returned field's
`FieldAvailable`; it is not a supplied future load. The live branch uses
`FieldAvailable.receipts` and `accessor_correct`. These derive the actual
load, stored-value readiness, raw readback, normalized constructor
receipt, own payload, and operation growth. `combine_correct` then derives
successful completion, ready combined output, exact payload combination,
valid operation tables, and `Grows`.

The prefix receipt should state the literal returned state, whole-native
equality, `Ready`, the SAME `At`, physical `Effects`, and exact operation
`Grows`. Its pure semantic field should state

```
Sat term combined.payload <->
  Sat term inherited.payload /\
  GuardReadback.Sat term (sourceEqualities returnedRawConstraint)
```

The live branch follows `InheritedPayload.combine_exact` and
`InheritedPayload.classes_sat`, with the accessor's exact readback. The
contradiction branch is false on both sides. This is a finite local
allocation theorem. It needs no recursive child completion premise,
whole-child closedness, guard-conjunction law, or final-state invariant.

Do not use `PartialPrecheckAllocation.run` as this prefix. It implements
the local precheck and has different operand order and return branches.
The inherited child prefix needs the returned edge's full own accessor
followed by inherited-first combination.

## Actual indexed child graph

The next operational graph should retain the actual current caller state:
full checked native/equality state, inventory, warm merge result memo,
current fourth memo, all three global tables, and the separate outer and
reduced-edge result tables when those are introduced. A current recursive
node `Call` must be an actual graph, not an arbitrary callback preserving
the desired result law.

The small reusable indexed core can have this shape:

```
Walk combined index (child :: rest) before ...
  -- actual descend combined index before.checked.operations
  -- advancePhysical to that exact returned operation state
  -- actual recursive Call descended child at that state
  -- Walk combined (index+1) rest at the exact returned caller state
```

The nil branch returns the literal same state and empty list. The
contradiction `Children` branch returns a same-length empty list, with no
descent or child `Call`. The live branch starts `Walk combined 0`.
Combination occurs before this graph and only once.

Use `ConstraintMemoAllocation.descend_correct` at each reached prefix.
The combined ready value is retained into the next child's operation
cache by actual `Grows.constraint_growth` and `ConstraintAllocation.Ready.grows`.
The child payload is exactly `SourceEqualityDescend.descend
combined.payload index`. Its live identity is the actual stored identity;
do not re-normalize or allocate a separate payload for the outer memo key.
`PartialPayloadAllocation.childInheritance_prepare` illustrates this key
readback, but its target worker state is historical and must not be used
as a current checked-state execution theorem.

The graph should preserve explicit accessor errors, missing fields,
recursive errors, pending/busy observations, and fuel exhaustion. An error
or unfinished head must not execute its suffix. Initial physical validity
derives that the allocation-only prefix succeeds. It does not derive that
every recursive child call completes.

## Physical and semantic preservation endpoints

First prove preservation for an actual current indexed graph. The
recursive node branch should supply its law through the actual mutual
proof. The public endpoint must not assume its own body completion or
future semantic receipt.

Required physical conclusions are: final `Ready`, computed final `At`,
physical `Effects`, old-child residency retained, result `Values`, exact
length preservation, returned operation validity/growth, warm merge
`Stored` and uniform `CacheCovers`, merge and fourth retention/correctness,
and exact ordered global reads with final global validity. Keep all
actual returned tables. Do not assert that native tables/domains are
unchanged through a recursive child: its reached native queries can
change them or execute a reset. Exact unchanged native-table statements
are appropriate for the allocation-only prefix and raw rebuild only.

For independent language, the useful node law is unconditional narrowing
and equivalence under its exact inherited payload's `Sat`. The indexed
walk then gives forest narrowing and equivalence when the parent term
satisfies `combined.payload`. The child satisfaction step is already
proved by `SourceEqualityInheritedPayload.combined_child`; use the actual
term at the actual index. `SourceEqualityDescend.descend_wellFormed` and
`descend_sound` retain the source trie representation and satisfaction.
No closed-whole-forest premise is needed for these pure arguments.

At the edge level, retain the exact returned raw guard. Accepted guard
semantics supplies own equality satisfaction via
`InheritedPayload.own_complete`/`GuardReadback.accepted_sat`; combining this
with inherited satisfaction supplies the child `Sat` premises. The edge
conclusion is unconditional narrowing and equivalence under inherited
satisfaction. If the combined payload is contradictory, an accepted
original guarded parent together with inherited satisfaction is
impossible. Do not claim that erasing a ZERO-child forest alone gives an
empty language: the empty forest still matches the empty term list.

## Raw rebuild versus checked parent construction

`Interned/Type.hs:394–400` uses raw `internEdge` when replacement length
equals `edgeChildren edge` length. Prove the indexed graph's length theorem
first. Then `EqualityLeafProjectionSetChildren.same_arity` supplies the
exact raw `makeEdge` branch, preserving the RETURNED symbol and full raw
constraint. It performs no second arity check, accessor demand, or Top
allocation. The checked fallback remains unused.

The current parent `mkEdge` is different. It is modeled by
`SourceCurrentAllocatedMkEdge.build`; it may access equalities, grow the
operation state, or allocate the Top sentinel. The inherited continuation
must not call this constructor again after its length theorem.

`SourceCurrentAllocatedMkEdge.reject` and its `RejectReceipt` return Top
and exactly `[.empty]` (`Interned/Type.hs:541–544`). The continuation must
load this returned Top field and traverse this singleton, rather than
retain the rejected original guard or its original arity. In the live
inherited case the actual `reducePartially'` request on that empty child
is still present. In the inherited-contradiction branch no child request
is present. Both branches preserve the sentinel's singleton arity at the
raw rebuild. The sentinel field was allocated by the checked parent;
availability derives its current load and does not justify resetting the
equality interner or injecting an initial Top-coverage premise.

For raw rebuilding, derive physical effects from the actual `makeEdge`
primitive, existing required-cache/semantic/cost/annotation laws, and the
current returned-guard `FieldAvailable`. Advance the full checked state
with `advancePhysical`; use `ClassScan.advance_ready` and `At.advance`.
`AllocatedMkEdge.raw_physical` is private, so it is a proof template, not
an exported general helper. This rebuild preserves the same inventory and
all current memo tables. Recursive calls before it can have changed both.

## Completion and memo boundaries that remain open

Finite allocation, finite list traversal GIVEN finite actual child
requests, and actual-graph language preservation are distinct from
general recursive caller completion. The source itself states the missing
termination argument at `Equality/Operations.hs:119–142`. In particular,
mixed-length classes can move a constrained node deeper through an
unconstrained Mu unfolding. Repetition of passes is also not proved.

`SourceEqualityInheritedGrowthBoundary.actual_prefix`,
`not_local_length_bound`, and `first_not_literal_derived` are checked
obstructions to an original-guard path-length/annotation-closure bound.
They do not prove an infinite reachable current caller run.
`SourceEqualityPartialHeightBoundary.not_parent_height_bound` is a
retained historical execution counterexample to a naive parent-height
argument. A current-policy execution transfer is separate; do not claim
that historical trace already uses the present gate.

The current outer source tables are
`genericReducePartiallyCache` at Operations.hs:72–81, keyed by inherited
constraint and original node, and `genericReduceEdgeIntersectionCache`
at149–168, keyed by inherited constraint and original edge. Current
`AllocatedParentEdge.Edge` covers the EDGE BODY, not the second memo
wrapper. It also does not implement the first wrapper or its recursive
child requests. Both need exact original arguments, physical identity
readback, hits that skip their bodies, source first-writer selection, and
protection of active producer frames. Do not merge these tables with the
native intersection node/edge tables, the warm merge memo, the current
emptiness memo, or the three global gate/unfold tables.

`Interned/Memo.hs:91–93,120–128` and `Interned/Cache.hs:134–155` publish a
lazy value without forcing its body and reread the winner outside the
update. The completed equality-operation tables model ready entries;
their allocation laws do not prove pending publication or GHC demand
equivalence. Historical `PartialMemoWorker`, `PartialMemoFrame`,
`PartialMemoSound`, and `PartialAllocationFrame` give useful independent
frame/key/immutable-language facts. Their old native state, closed-cell
invariant, and historical local body are not a current execution adapter.

The source `ChildIndex` is an `Int` (`Data/CFTA/Index.hs:41`). Existing
Lean descent indices are `Nat`. Keep a representation/fit boundary for
the actual zero-based enumeration, separate from reached native
`WordRanges`. Existing local range plans must apply at the literal
returned checked states, not at a cold or reconstructed state.

## Independent current parent-edge review

Reviewed frozen `SourceCurrentAllocatedParentEdge.lean`, SHA256
`415caf6fc59d1c04d64ae93c51e4932c26e8031c84733e3caa622cbb5e008549`.
No material defect was found. The review checked all constructors,
`rejected`, `finite`, the `Reads` schedule, and the complete `Receipt`.

The raw contradiction branch skips local reduction and has a separate
public endpoint without child availability, field-load, inherited-ready,
or local-range premises. The live branch uses the SAME actual local
reduction return and then `AllocatedMkEdge.build` at its returned checked
state. The original stored field and load are transported by actual
operation growth. Constructor effects preserve the returned merge,
fourth, and global invariants. No operation cache is reset.

`Receipt.construction` correctly distinguishes direct rejection from a
local same-length child return followed by checked construction. It does
not claim that the final checked edge has the original arity. Its
language narrows unconditionally and is equivalent under inherited
satisfaction. It assumes neither a result language law nor a completed
local reduction. The finite theorem constructs the latter from initial
invariants and reached ranges. Returned-edge symbol/guard/children facts
can be read from the exact nested constructor receipt. Outer inherited
children, reduced-edge result-memo publication, general recursive
termination, and GHC evaluation order are explicitly outside this module.

Observed existing owner evidence: `parent-edge-build-1.log` reports
terminal success with 1,390 jobs and only the old unused-input warning.
`parent-edge-public-probes-1.log` contains the public probes. Those checks
were not rerun by this independent read-only review.
