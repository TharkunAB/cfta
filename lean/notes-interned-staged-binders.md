# Staged generated nested binders

`InternedStagedBinders` constructs nested Mu values from finite source syntax.
It uses the separate edge and node caches, exact two-probe construction,
complete record readback, and smart cleanup from the preceding modules.

## Concrete fragment

`Skeleton` contains the local recursive argument, numbered capture slots,
ordinary nodes with ordered edges, and unions. It has no callback that can
inspect a reference identity. `Program` constructs a finite list of dependency
programs first. It then inserts their complete results into the capture slots
and executes an ordinary template or a Mu template.

Dependencies can themselves contain arbitrarily many such stages. Thus Mu
values can occur inside other Mu bodies. Each dependency is independent of
the fresh recursive argument of its enclosing stage. The program syntax
cannot inject an arbitrary `Value`, canonical identity, or metadata record.
An out-of-range capture slot denotes `EmptyNode` explicitly.

The schedule is dependency-first. A source program can enforce this schedule
by evaluating its captured dependencies before invoking the enclosing Mu.
For example, evaluate `inner`, then construct:

```haskell
Mu (\outer -> Node [Edge 1 [outer, inner]])
```

This model does not claim that an arbitrary lazy `let` expression uses this
allocation order. An unused dependency can be forced by this schedule even
when an unforced Haskell binding would allocate nothing.

## Derived results

`build_constructed` and `buildMany_constructed` derive the actual finite
constructor trace by recursion on the program syntax. `empty_build_correct`
then derives complete key-to-record coherence from empty caches. It does not
assume that the resulting graph has the desired invariant.

`dependencies_complete` proves that all staged dependency payloads have
completed before the enclosing Mu starts. `normalized_body_pending_safe` derives that
its body computation, including root self-reference removal, cannot request
a Mu record. A captured Mu is
already a complete value; reading it does not issue another Mu request.
This is the specific reason that pending-key collisions cannot occur in
this fragment.

`build_replay` and `empty_build_stable` preserve the whole result and the
whole state after later table growth. This includes both counters, all
metadata, and all stored body and probe records.

`family` collects the program and its recursive dependency programs directly
from syntax. `records` retains their actual results at the states where the
root execution computes them. `family_replay` proves that a single root
execution fixes the later result of every family member. It does not require
an additional warmup pass or a supplied finite-family stability law.
`finite_identity_image` gives the resulting finite identity image, unchanged
state on every later request, and the exact syntax-family length bound.

`twoBinders_metadata` checks a productive inner Mu captured by a productive
outer Mu through kernel evaluation. The result has Mu depth 2, no free
references, six edge allocations, and eight node allocations. This checks
the generated nested path through both cache families and all three body
applications per new Mu.

## Remaining boundary

The fragment does not rebuild an inner binder from a fresh enclosing `Rec`
reference. That source case requires a stronger argument: each inner Mu key
must differ from every pending outer key, or already have a complete record.
Its proof must also establish the provenance and freshness of captured outer
references. Neither callback totality nor complete records at stage entry
implies this property for an arbitrary nested callback.

The finite family is the actual staged program family. It does not yet cover
every environment-dependent request from the general `substitutionPlan` or
epsilon exposure traversal. The module therefore does not claim a complete
runtime traversal bound for general recursive source automata.

For an already completed Mu, source `matchMu` reconstruction can avoid this
pending-key issue. It reuses the stored depth probe and, when the depth-probe
and actual-body depths agree, the stored ordinary probe. The resulting key
then hits the completed original record. The existing
`InternedBinderProtocol.matchMu_cached` theorem states this step. Deriving
that depth relation for all generated nested callbacks remains separate.

Validation on 2026-10-12: `lake build MicroCFTA.InternedStagedBinders`
passes with 108 jobs. All 16 theorem axiom checks use only standard Lean
axioms. No new axioms, incomplete proofs, Haskell edits, or Cabal runs were
added.
