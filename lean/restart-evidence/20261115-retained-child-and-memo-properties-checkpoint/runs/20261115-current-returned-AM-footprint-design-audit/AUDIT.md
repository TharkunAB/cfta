# Actual Returned-law design audit

Status: READ-ONLY DESIGN AUDIT. No new theorem or compiler credit.

The existing `Returned` parameter can express the required conditional A/M result property. It does not need a new cache framework. The missing work is an actual producer and history proof that retains the genuine mixed-call pattern and height bound. Physical validity does not supply that proof.

The copied original coupled header is byte-identical. Its historical OPEN comment is retained. The literal-kernel coupled theorem is already public. This audit does not transfer that result to `SourceEqualityNativeDemand`.

## Minimal fixed result law

Fix the accepted original source, its build, and the full stored value `U = mu entry body depth ordinary`. Let `uid = entry.identity`.

The following equations specify the property. They are schematic mathematics, not Lean declarations:

```
OnlyU(v) := forall a in atoms(v), a = mu uid
Profile(v) := v.free = [] and OnlyU(v)

A(r) := r.domain = emptyDomain and Profile(r.left) and Profile(r.right)

NodeLaw_W(r,v) :=
  (A(r) -> Profile(v)) and
  (forall authentic witness w in W, M_w(r) -> Profile(v))
```

`Returned NodeLaw_W state.nodes` uses the existing definition directly. The law concerns the exact cached original request and the exact returned value. It does not assert availability in a future heap. Weak physical cache validity supplies availability separately. The actual ready/finish consumers retain both properties.

`W` must describe authentic original entry data. For each witness, retain:

- The complete original `pattern`, its `patternId`, the original heap and domain cache, and the exact `entered = Environment.enter domains emptyKey U pattern uid patternId`.
- Facts and source growth for that original heap; original pattern availability, closedness, identity, and node/union tag. **There is no only-U premise on the original pattern.**
- The original initial machine `⟨heap, entered.2⟩`. At use, derive the actual continuation `Extension initial later`, including heap records, issued identities, and domain entries.

`M_w(r)` keeps the literal equality `r.domain = entered.1`. In either operand order, the other fields are exactly `(openAlias, operand)`, where:

```
openAlias = body or openAlias = reference(interned uid)
Profile(operand)
height(operand) <= height(pattern)
openAlias = reference(interned uid) -> height(operand) < height(pattern)
```

Actual request readiness gives operand availability at the actual later heap. A real history proof must connect that machine to the witness's original initial machine. An identifier match alone cannot replace that connection. Do not rebase the original entry when applying the genuine smaller-fuel M hypothesis.

An equivalent law is `(A(r) or exists w in W, M_w(r)) -> Profile(v)`. Universal witness notation makes it clear that selecting a convenient fabricated pattern is not allowed. Neither form assumes a model, inhabitant, future completion, or successful request.

## Existing laws to reuse

`SourceCurrentAllocatedNativeContextCache.Returned` already quantifies over the complete request stored at each returned cell. Its public `returned_empty`, `returned_lookup`, `returned_demand`, and `returned_finish` proofs are property-parametric. The actual `node_ready_property`, `edge_ready_property`, `finishNode_property`, and `finishEdge_property` consumers preserve exact physical cells and operations.

A producer proof must supply `NodeLaw_W request actualResult` to the existing finish law. It must also preserve Returned at every supplied-fuel endpoint. A completed-body result alone does not prove propagation through pending or stopped prefixes. The empty/self all-fuel packet is a separate, currently uncredited candidate; it does not establish the recursive A/M producer family.

For the edge memo, use the same framework with a conditional row result law: every returned child has `Profile`, when the actual ordered child requests satisfy the original A/M qualifications. Retain the real domain and ordered child pairing. The mixed body/ref case needs M for its open ref children; requiring only closed A children would omit the essential case. The actual edge producer, allocated field callbacks, and all prefix outcomes still need proof. This audit adds no edge framework or public edge predicate.

## What existing history helpers retain

- `KernelFacts.Extension` retains heap growth, issued-identity history, and domain-table extension. It is the existing transport to reuse.
- `Environment.enter`, `entered_bindings`, and `enter_correct`, together with `Domain.AvailableBindings` and `lookup_mu`, retain the actual U binding and domain representation. `AvailableBindings` concerns free Mu names. It does not retain the complete non-Mu pattern.
- `RequestScope.NodeScope` retains original syntax and physical availability for both current operands and original free bindings. `NodeScope.mu` transports those facts through the actual entry expression. It does not state the original pattern-height relation for a later body/ref request.
- `NativeOriginalRequestScope.RootedScope` retains source writers for current Mu operands and free bindings. It does not identify the original non-Mu pattern or its height bound.
- `ContextRebase.SeenCovered` and `AdmissionCache.NodeCovered` retain admitted nonempty input representatives for both identities of every seen pair. `InputInventoryModels.reachable_original` can recover complete original available records from the appropriate actual fixed-source reachable inventory. These facts are useful. They do not alone identify the original U/pattern role and prove that the current Q has the required height relation to that same pattern.
- `NativeRequestSourceScope.node_prefix` derives fixed-entry-source scope for actual reached checked-code requests. Its explicit word-range and domain-room bounds must be discharged in the existing scope; they cannot become new whole-goal assumptions. This helper offers a possible way to derive authentic pattern availability without a separate witness ledger.

The precise remaining history obligation is therefore an actual request-admission induction: at a real U/pattern entry, retain the full genuine pattern and exact domain; through the real swap, body/ref, union, child, reset, lookup, and memo operations, derive the A or M qualification for the actual request, including the strict ref height bound. Use existing physical source scope and pair coverage to discharge provenance where they apply. No inspected helper already proves this complete implication.

## Counterexample to an overbroad qualification

Reject this candidate:

```
exists arbitrary raw P with identity(P)=pid and node/union tag,
  domain matches enter(U,P,uid,pid) and height(Q) < height(P)
```

It omits physical availability and authentic common history. `Environment.bindings` adds bindings only for Mu operands. For a node or union pattern, `enter` sees its supplied identity pair but does not inspect its payload or height. Replace a real closed ordinary pattern `Q` by a taller raw node `Pfake` with the same identity and changed edges. The raw enter expression has the same result, but the forged height makes `Q < Pfake` pass.

In the actual domain entered for `(U,Q)`, the request `(Q, ref uid)` has the already seen original pair. Under the actual nonempty/no-reset/non-self/order conditions, `Control.repeated_first` selects it and `repeatedValue` is `reference(intersection uid pid)` up to the canonical pair order. This result is open and has a non-U boundary atom. The genuine M statement excludes this case because its real original pattern is Q, so the strict height inequality is impossible.

This is a counterexample to the raw existential qualifier. It is not a claim that the accepted source worker reaches the bad request. `MixedDescendantFreshness.closed_identity_injective` rules out the forged complete node when both records are available in one coherent heap. Two unrelated extensions of the source snapshot do not suffice: they can assign the same fresh identity to different records. Use an actual common continuation and issued-history proof.

## Fixed-law and scope cautions

For a fixed collection of captured past witnesses, Returned needs no change. If the collection grows, preservation for the old law does not automatically establish the stronger new law for old returned cells. Prove compatibility or derive the new qualifications from actual earlier producer history. Defining W from future observed successful results would be circular.

A fixed-source alternative may avoid an evolving ledger: qualify patterns by complete availability in the actual query-entry source and prove exact domain replay plus the original height relation from the actual trace. The existing source-scope and seen-coverage helpers supply parts of that route. No such complete replay/admission theorem is claimed here.

The genuine recursive checked-code body/ref producer proof remains OPEN. The original source-no-Mu and no-handle cases are unchanged. This audit proves no semantic typing, narrowed-domain membership, compatible assignment, termination, or whole-worker correctness.
