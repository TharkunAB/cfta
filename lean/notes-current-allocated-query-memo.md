# Checked query state enters the current conjunction memo

Source main is `78618ea2`. The source refresh changes the derive frontend.
It does not change the native intersection or conjunction bodies.
The optimized interned core and all older proof definitions remain intact.
The full-library goal remains active.

## Actual checked heap effects

`SourceCurrentAllocatedNativeSemanticHeap` derives `SemanticReady` through
actual checked work, optional binding, one step, and every finite outcome.
Its minimal input plan checks current work operands and available optional
bodies. Open available bodies are permitted. Errors and blocked outcomes
retain their actual returned heaps.

`SourceCurrentAllocatedNativeCosts` derives the stored `CostHeap` invariant
through those same operations. It needs initial readiness and costs, not a
completed query or future costs. This invariant concerns stored unfolding
observations. It is not a bound on elapsed time or total native work.

`SourceCurrentAllocatedNativeEffects.execute_effects` combines those results
with loaded-field closure and checked validity at the same returned state.
It derives physical retention, operation-cache growth, final readiness,
checked native validity, and the actual yielded continuation's field facts.
The richer reached input plan still includes word checks and semantic
`NodeProduced` or `EdgeProduced` receipts at finish controls.

## Completed query and current memo

`SourceCurrentAllocatedQueryMemo.query_effects` takes an actual completed
checked node query and that reached input plan. It derives result availability,
physical effects, and checked node provenance. Exact key checks exclude the
unresolved direct branch. Warm hits use the original returned cell. Started
calls use actual checked body readback and the original finish handle.
The stored `NodeProduced` receipt includes an actual checked body execution.
Its existential receipt states are not asserted to equal the current body's
states.

`advancePhysical` keeps both full native memo tables and the domain cache.
It advances only the constructor heap and equality-operation cache returned
by the new conjunction call. Physical retention transports stored native
receipts and the existing emptiness memo to that actual heap.

`finite_after_query` constructs a new `SourceCurrentConjunctionMemo.Call`
after the completed query. It derives full returned readiness, checked native
validity, idle tables, fourth-memo correctness, conservative answer soundness,
old-entry retention, and the node receipt at the final heap. It assumes no
future field loads, result availability, final readiness, or completed
conjunction decision. It does assume query completion and the reached input
plan. A true answer excludes every common original input term for closed
operands in the exact empty domain. False remains inconclusive.

## General checked completion prerequisites

`SourceCurrentAllocatedNativeRunning` follows actual completed checked traces.
It proves that no new evaluating cell remains. Initial idle tables therefore
return idle tables. Actual node and edge completion restore the enclosing
active bound. The proof uses no old native execution or semantic callback.
It is a lifecycle theorem for completed traces, not a completion theorem.

`SourceCurrentAllocatedNativeRequestBounds` derives strict child bounds from
the independent original-input `requiredFuel` measure. Accepted code contains
only the original ordered zipped child requests. Rejected and mismatched
sentinels contain no recursive request. The actual checked body prefix derives
its emitted code bound at its returned state. This can use a larger semantic
schedule without replaying skipped child effects.

Its `Words` and `WordRanges` inspect actual checked yielded prefixes.
Transfers retain exact full states through steps, binds, and body prefixes.
These predicates do not generate range proofs or semantic finish receipts.
Their node check is conditional on a represented key. The richer validity
input plan still requires its full current node check.

## Remaining work

Derive general finite checked queries from initial invariants by induction
on the independent request measure. Derive reached physical inputs and the
semantic finish receipts. The closed-only `NodeMeaning` law is vacuous on
nonempty recursive domains. General recursive `Mu` results need adequate
open-context soundness and completeness laws. Exact `SeenContext` cannot be
extended to every optional-binder candidate: `seen_override_forces` restricts
that candidate to one fixed operand intersection. Do not assume that false
extension law or substitute an old eager execution.
Returned warm cells currently carry only the closed/empty-domain language
law. A general open-context result needs a stronger preserved cache invariant
or an adequate causal-history proof. A stored historical body receipt does
not supply its initial semantic cache invariant.

Compose original whole-heap allocation histories with checked query entry.
Then define the new current class Scan and connect the exact physical caller.
The historical intersection-based Scan remains a different body. Continue
general constrained outer completion, whole enumeration/import, templates,
typed refinements, heterogeneous generators, public interfaces, and every
separate Sized contract. GHC forcing, pending publication, concrete containers,
machine capacity, runtime identity, and concurrency remain separate boundaries.

## Validation

The pinned full audit passes 2,254 jobs and checks 55,292 theorem dependencies.
Forty-eight public axiom probes, thirty-six endpoint signatures, and fifty
literal kernel examples pass. Two additional named kernel theorems occur in
the running and request-bound probes. Only the three standard Lean foundations
and the preexisting unused-input warning occur. Independent review found no
state-threading or conservative-soundness defect.

Seven new Lean modules and two scope notes retain all older non-Audit proofs.
Audit gains three imports. The refreshed Haskell source passes the strict
Nix build and all six suites: 767 examples plus the golden check. Fourmolu
checks the four changed Haskell files with the updated fixities. Cabal-gild
checks all four active packages. No new test file is committed.

Evidence uses `/tmp/mcfta-allocated-query-*`, the semantic/cost/running/request
validation reports, and `/tmp/mcfta-derive-78618ea2-*`. The closing preservation
report records all prior files, sixteen external marked drafts, stashes, and
other worktrees. This checkpoint does not complete the full-library goal.
