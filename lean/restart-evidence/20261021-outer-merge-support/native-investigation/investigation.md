# Stored Mu positions: bounded source investigation

Written 2026-10-21 02:35 CEST. This is an unchecked theorem proposal and a source audit. It contains no Lean commands, new proof, production edit, or concrete source-built counterexample.

## Recommended first theorem

For the concrete Symbol/Guard aliases of SourceCurrentRequiredPositivePosition, propose:

```lean
theorem publication_binderFree_positions
    (event : SourceCurrentNativeMuPublication.Publication)
    (firstOrder : InternedStoredShallowCompletion.BinderFree event.expression)
    (path : List Nat) :
    SourceCurrentRequiredPositivePosition.PositiveAt event.body path ↔
      SourceCurrentRequiredPositivePosition.PositiveAt event.ordinary path
```

This statement fixes the SAME actual publication, expression, captures, ordinary level, reservation and all callback heaps. Its premise is a syntactic restriction, not the desired output relation. The theorem must derive the relation from event.context, event.depthDone, event.ordinaryDone and event.bodyDone. It must retain the body of the historical selected writer. It must not compare a later requester callback with an earlier winner body.

The one-way consequence from body to ordinary is sufficient for the requested backward position handoff. The two-way target is a useful constructor induction invariant. BinderFree applies to the callback expression only. Captured inputs may contain full Mu values; the inputs stay identical, and PositiveAt treats each Mu as opaque. This does not establish the full nested source law or an arbitrary native call law.

## Why this is an actual producer

InternedFreshOrdinaryConstruction.build, lines100–113, executes the same lexical callback three times. It first uses Depth, then uninterned(ordinaryLevel depth), then the actual fresh interned entry. Every callback builds the SAME source body with the SAME captures and applies withoutSelfReference to the exact returned value. NativeMuPublication.Publication, lines21–56, retains these exact calls and the missing-key reservation. SourceCurrentConstrainedCapSourceHistory.Context, lines22–27, supplies actual available captures, normal/coherent records, free-name/profile heaps and the depth heap.

For BinderFree syntax there are no nested request/finish steps. InternedFreshOrdinaryFirstOrderHeap.callback_noNewMu, line22, confirms this physical boundary. A simultaneous structural proof can pair the two actual completed callback executions. Fixed capture slots contain the exact same complete value. Both varying local slots are literal nonempty references with no PositiveAt. Keep matching actual empty-child decisions together with the same-path positivity relation. For ordinary rows, use literal source child order, actual makeEdge/readback and canonical surviving full rows. For unions, use exact member flattening and normalization. Canonical order or duplicate rows can change row indices; they cannot justify changing a child index or the path. Literal root filters remove only bare reference alternatives, which carry no PositiveAt. Filter cleanup must be proved directly; no whole-callback equality is available.

The recent private makeNode_positive, ordinaryUnion_positive and makeUnion_positive helpers provide the backward physical constructor direction. A paired proof also needs the selected surviving-row direction and matching child emptiness. It cannot obtain that direction by applying the backward helper twice. Thus this proposal is feasible and source-grounded, but not already proved by those helpers.

## Existing scalar proof and the missing nested obligation

GuardHeap.Correct, SourceCurrentConstrainedCapGuardHeap lines21–22, is equality of one Option Nat profile. GuardExecution.build_profile, line124, derives this scalar observation by actual syntax induction. Its request_heap proves each fresh candidate and complete_heap keeps an earlier first-writer certificate. closed_heap, line341, derives the scalar heap from actual empty source construction, including pending stopping states.

GuardSemantics.Shape has structural reference/depth information and a single guardDepth field. It does not retain child-index paths. Distinct nonplain occurrences at sibling indices0 and1 can have the same maximum guard depth. Equality of guardDepth, root/free-name profiles, or decoded depth therefore cannot prove PositiveAt body path implies PositiveAt ordinary path. This is a logical information loss, not a new checked source-built defect.

For nested syntax, a recursive smart binder can return the BODY OF AN EARLIER WARM WRITER. Existing Context and Origin retain exact callback execution and scalar/depth/free-name facts. They do not contain the required pointwise position law for that earlier payload. No existing result inspected supplies that missing law. A Publication by itself must not be treated as a completed empty-source history with the stronger invariant.

The full unchecked target is a state-independent stored invariant:

```lean
PositionCorrect entry body depth ordinary :=
  ∀ path, PositiveAt body path ↔ PositiveAt ordinary path
```

The useful actual producer is a new closed_heap analogue:

```lean
∀ source,
  SourceCurrentPublicationHeapInduction.Heap PositionCorrect
    (InternedFreshOrdinaryConstruction.build source [] empty).state
```

It should also have a warm build preservation endpoint from initial PositionCorrect heap plus the actual initial Context. The final empty-source corollary must derive, not assume, its initial heap. No completed final result is necessary because publication occurs before the stopping outcome.

A proof route is to extend the existing joint source semantics with a predicate on List Nat while retaining its structural empty/local-use observations. Ordinary rows add their guard at [] and prefix each child predicate with its exact natural index. Union combines alternatives without a path step. Raw or retained smart Mu has no positive paths. Unused smart cleanup retains the body's paths. Reference and Empty have no paths. Derive callback observations and fresh-candidate body/ordinary agreement together with the heap, following GuardExecution. Reuse PublicationHeapInduction.path_heap only AFTER deriving the candidate publication law; that generic induction is not itself the missing proof.

## Exact cleanup and warm-hit consumer

The minimal intended stored readback contract is body-to-ordinary at the SAME path. InternedProfileHeap.stored_probes, line60, derives the exact complete stored probe values under physical Facts and Available current probes, including warm cache hits. It supplies no body position law.

For a full stored Mu, cleanup in InternedConstructorTemplates line631 either returns its body, returns Empty for a bare self-cycle, or retains the opaque Mu. Therefore any PositiveAt of a smart cleanup return can only come from its stored body. With PositionCorrect it transfers to that SAME writer's ordinary probe. DepthHeap.Correct can additionally relate the cleanup branch to usesLocal depth ordinary, as GuardReadback.finish_profile line27 already does for scalar profiles. A useful precise future equation is:

```lean
PositiveAt (finish smart (.mu entry body depth ordinary)) path ↔
  (smart = true ∧ usesLocal depth ordinary = false ∧ PositiveAt ordinary path)
```

This equation additionally needs the actual decoded depth invariant. It is not a premise for the first BinderFree theorem. A one-way result-to-ordinary handoff can avoid naming the decoded local-use flag. The unused maybeMu bypass, where the pair name is absent, returns its input body directly and has no stored-writer issue.

## Boundaries

No actual completed original-source counterexample to the pointwise law was found or proved. No full nested pointwise law is claimed. No arbitrary Good, scalar GuardHeap equality, heap Grows, causal history, or exact Origin is upgraded to a position invariant. Nested encode may contain binders for OPEN Mu records (InternedStoredSubstitution.encode line58); closed captures become slots. Therefore the BinderFree result must not be applied to all generated encodings without proving BinderFree for that actual expression. No global renewal rank, termination, Haskell refinement, or current/requester body equality follows from this local foundation.
