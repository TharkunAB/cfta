# Scope of recursive Root support

Reviewed on 2026-10-18. This is a source review. It adds no production theorem
and runs no Haskell or Lean execution.

## Result

Public smart Mu construction does not imply `SourceMemoGate.unconstrained =
true`. Constrained recursive values are valid public inputs. The new `Root`
premise is an explicit local support condition until an actual gate or an
annotation producer discharges it. This is not a Haskell defect.

`Root` is local to the selected value. Ordinary nodes and Empty satisfy it
without any guard restriction. A Mu or union root must pass the source gate.
A bare reference also passes that syntactic gate, but this does not make a
nonempty Required call on the reference succeed. The predicate is not a
whole-forest plainness or complete execution-domain assertion.

Source: `lean/MicroCFTA/SourceCurrentActualRequiredRowOrigins.lean:28-31`.

## Public constructors and readers

`Data.CFTA.Interned` exports the Mu pattern, createMu, createMuDontCleanup,
nodeEdges, and unfoldOuterRec. The Mu pattern calls createMu. Smart cleanup
removes an unused binder or a bare-self body. It performs no unconstrained
check. The root-union filter removes an immediate bare-self alternative.
It does not remove a constrained ordinary row.

The documented callback precondition is invariance under renaming. It is
not a constraint-free-body precondition. Original construction therefore
permits a used self reference below an ordinary positive-guard row.

Sources: `cfta/src/Data/CFTA/Interned.hs:10-34`;
`Interned/Type.hs:671-697`, `:721-753`.

`unconstrained` checks every reachable ordinary edge for empty equalities
and no residual guard. Its crush visits a Mu body, not either probe. The
predicate is a separate read. `nodeEdges` and unfoldOuterRec do not require
it and can expose constrained Mu bodies.

Sources: `cfta/src/Data/CFTA/Enumeration.hs:529-549`;
`Interned/Operations.hs:110-128`, `:144-181`.

## Minimal public smart-Mu counterexample

```haskell
same = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
constrained = Mu (\self ->
    Node [Edge "a" [], mkEdge "p" [self, self] same]) :: Node Symbol
```

The class is consistent, nontrivial, and fits the binary row. mkEdge retains
its complete constraint. The self reference occurs below the pair row, so
neither smart cleanup case removes this Mu. The body is not a root union.
The source crush visits that pair row. Its equality field is not empty.
Thus `unconstrained constrained` is false by the listed definitions.

This is a source-derived expression, not a newly executed diagnostic or a
new kernel theorem. The existing public-constructor test at
`cfta/test/Data/CFTA/EqualitySpec.hs:728-734` already uses this form with an
additional nontrivial equality class. It does not rely on forged interned
records. This review does not claim a fresh test run.

Constructor details: `Interned/Type.hs:554-585`;
constraint construction: `cfta/src/Data/CFTA/Constraint.hs:212-213`;
class normalization: `cfta/src/Data/CFTA/Equality/Constraint.hs:352-381`.

## Lean construction and annotation guarantees

`SourceRecursiveIntersectionInputView.Original` restricts payload references
to complete interned names. Its node case does not restrict guards. Its Mu
case requires only Original of the body. It does not imply Root or a plain
gate result (`SourceRecursiveIntersectionInputView.lean:246-255`).

Closed repaired source construction completes for arbitrary source syntax
(`InternedFreshOrdinaryClosedCompletion.lean:43-53`). Its completion theorem
does not add a plain-body restriction. Causal GuardHeap Plain records Mu
body/probe profile equality. Both profiles can contain the same positive
rows. It does not imply that the selected Mu passes the gate.

There are precise conditional gate producers:

- `SourceCurrentHereditaryUnconstrained.unconstrained` derives the gate from
  hereditary Plain annotations (`:125-129`).
- `SourceCurrentGatePlainRegion.annotations_iff` equates those annotations
  with the actual gate on coherent available input (`:59-65`).
- `SourceEqualityAnnotationConstruction.closed` constructs annotated values
  only when the source syntax satisfies its Allowed predicate (`:132-146`).

None of these asserts that arbitrary public smart-Mu input is plain.

## Actual primary selection supplies local facts

The source partitions classes using original `origNs` and the primary
`meetsConstrainedMu True` read. A constrained Mu is refused. A plain closed
Mu passes. A plain open Mu is followed through its unfolding. The endpoint
also tests whether an ordinary node reaches a constrained Mu.

Sources: `cfta/src/Data/CFTA/Equality/Operations.hs:213-226`, `:246-270`;
`lean/MicroCFTA/EndpointStatefulGateTrace.lean:20-40`.

An actual false primary trace therefore supplies gate acceptance at an
encountered Mu. Existing `SourceCurrentRequiredPrimaryExposure.node`
extracts this for a nonempty Needed Mu (`:84-110`). Its primary_domain
produces ExposureSafe from original false class traces and retained heaps
(`:194-207`). Its finite ordinary shortcut also requires UnionNormal.

At an actual false endpoint, `SourceCurrentPrimaryEndpointCap.endpoint_clear`
and endpoint_cap derive descendant exclusion and a finite local Cap from
the physical source (`:127-137`). These are selected endpoint facts. They
are not a global Cap restriction on all public inputs.

## Required identity and the later class fold

ExposureSafe.identity permits every value at empty Needed. In particular,
it permits the constrained Mu above. Root would reject that Mu. Therefore
ExposureSafe alone does not imply Root. Required identity leaves the value
unchanged. EditAt later applies its callback; EditBelow on Mu performs Head
without a new gate check.

However, an arbitrary constrained endpoint allowed by identity is not by
itself an active-original-class counterexample. The actual false primary
endpoint policy would have refused that constrained original value.

The source scans original classes once, then folds edits over updated
forests (`Equality/Operations.hs:213`, `:226`, `:236-242`). Primary replay
retains certificates for the same original literal values at larger heaps
(`SourceCurrentPrimaryReplay.node_replay:21-27`). It does not certify a new
value returned by an earlier class edit. The present review proves neither
that such an edit creates a constrained Mu nor that it cannot do so at
every later selected position. That universal transfer needs a proof.

For the tracked root under the disjoint untouched-child footprint, the
new class law already preserves Root through each actual below edit and
fold, once Root holds initially (`SourceCurrentActualClassRowOrigins.lean:
100-133`, `:191-225`). No extra Root premise is needed at every later class.
This is local preservation, not a statement about all generated values.

## Small next bridge

A false primary NodeTrace already implies Root for its input value.
Ordinary and Empty cases satisfy Root directly. Reference and union traces
cannot return false. Both false Mu cases retain the actual accepted gate.
This extraction needs no heap annotation or union-normality premise.

A false ClassTrace contains a false path trace for every original member
path. For a present original forest slot, that trace supplies the false
NodeTrace above. The literal checked primary worker already derives this
ClassTrace from its actual false return. This is a direct route from an
actual selection decision to Root for each selected original forest value.
It also covers an empty suffix after the selected forest index.

Separately, ExposureSafe at a nonempty Needed child map implies Root by
cases. Identity is excluded by map nonemptiness. This fact alone gives no
Root for untouched or empty requirements. Those schedules need a separate
identity Link result, such as Link.refl.

These are proposed local bridges in this review, not yet new theorems.
They do not certify values returned by arbitrary earlier class edits.
They do not prove all active-key exclusion, a bound on fresh recursive
requests, or general termination.
