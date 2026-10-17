# Positive-depth Mu guard-cap readback

Reviewed on 2026-10-17 at 04:00 CEST. This is an independent source audit. No production file changed.

## Finding

The current guard-language probe heaps do not provide syntactic guard-cap reflection. The source-origin heap retains the exact construction schedule needed for a new causal proof. It does not already contain that proof.

`InternedGuardedProbeHeap.Correct` at line 24 equates a raw stored Mu language with the least language of its exact ordinary probe. `hit_language` at line 57 exposes that equality at an actual canonical hit. The quantification over all guard interpretations and reference languages does not turn the statement into a syntactic guard observation.

`InternedGuardedBudgetProbeHeap.Correct` at line 19 adds local normality, raw budget-language equality, and empty-local body-language equality. `uses_eq` at line 55 recovers the deep-local decision from the existing depth heap. `hit_language` at line 88 selects the actual smart-finish branch. These statements preserve guard acceptance on productive terms. They do not inspect guards in nonproductive recursive branches.

`SourceCurrentConstrainedCapWarmOccurrences.hit_cleanup` at line 111 already proves that a maximal marked ordinary probe makes the actual warm finish return the stored body or empty. Its premises retain exact probe availability and the actual populated key. This result removes a retained wrapper. It does not derive the old body's guard cap.

## Verified source-built obstruction

`guard-probe-language-boundary.lean` constructs the literal generic source expression `binder false (node [edge 0 false [var 0]])` from the empty heap. The result is the raw recursive value with body `bad(self)`.

The imported kernel constructs its own completed source execution and derives availability, the current semantic heap, the semantic source-origin heap, and the guarded budget-probe heap at that exact return. It proves that the result has no finite cap for the predicate `guard = true`. It also proves that its guarded budget language is empty for every guard interpretation, reference environment, unfolding budget, and finite term. Thus all-budget language observations alone cannot reflect the syntactic cap.

This witness uses the actual generic constructor executor with Boolean guards. It is not an arbitrary coherent cache. It is not a Haskell behavior defect. It does not refute cap readback from exact causal probes: its own probes are also nonhereditary. It refutes only the proposed shortcut from extensional guarded language observations to syntactic cap.

The final kernel passed strict absolute-path checking in `guard-probe-language-boundary-4.log`. The log contains one explicit full-signature and axiom pair, no diagnostics, and no `sorryAx`. Failed attempts one through three retain their exact source snapshots and raw logs.

## Reusable exact source facts

`InternedProfileHeap.stored_probes` at line 60 recovers both exact stored probes from `Facts`, requested-probe availability, and the populated `muKey`. Numeric key agreement is converted to equality of complete available records. This is the correct warm-owner readback step.

`InternedFreshOrdinarySemanticOrigins.Origin` at line 22 retains one source expression and lexical environment, an initial `Context`, both actual normalized probe calls, the missing canonical key, the exact reserved entry, and the actual normalized body call at that entry. `complete_heap` at line 59 retains an earlier origin on the old-record branch and installs the candidate origin only on the new-record branch. `build_origins` and `closed_origins` derive this invariant through actual source execution, including discarded effects and pending outcomes.

The historical `Context` in an origin includes normalization, lexical availability, root profiles, and free-name observations. It does not include a historical `DepthHeap` or a new guard-cap profile heap. The origin also does not store a growth relation from its historical initial heap to the current heap. A new proof must not infer those missing historical facts from the current semantic heap. Reuse the origin's schedule while deriving the new invariant during actual writes, or explicitly retain the additional historical facts when those writes occur.

`InternedDepthSemantics.Shape` and `InternedRecordDepthShape.shape` supply exact root alternatives, emptiness, deep names, opacity, and cached depth. They discard every guard. They can select normalization branches in a new joint interpretation; they cannot supply its cap component.

## Smallest causal producer target

For a fixed guard predicate `P`, a useful conditional cell law has this shape:

```text
actual stored Mu(entry, body, depthProbe, ordinaryProbe)
  -> forall d,
     Cap P d depthProbe
     -> Cap P d ordinaryProbe
     -> usesLocal depthProbe ordinaryProbe = false
     -> Cap P d body
```

This is a proposed invariant, not a completed theorem. Assuming it as an arbitrary caller premise would leave the original problem open. Its producer must derive it from the same three actual callbacks before completion, then retain it for the current first-writer winner. At depth zero the existing causal `MuStored P` law covers hereditary body readback. Its positive-depth cases remain missing.

The concrete pure component under investigation by `arity_meaning` records the minimum finite cap, or no finite cap, together with the existing root/deep shape. Empty and reference values have minimum zero. Ordinary values have minimum zero when hereditary; otherwise they consume one layer above their children. Unions take the maximum member requirement. A nonhereditary stored Mu has no finite cap. The joint shape must account for empty-child edge deletion, root filtering, and smart binder cleanup. A cap number without these branch observations is insufficient.

The actual execution component must prove this joint observation for every returned source value and retain a corresponding cell law at every stopping state. On a fresh write it must derive the candidate law from the actual callbacks. On an earlier-winner branch it must use the retained old cell law. Source construction from empty can then produce the invariant without a desired stored-body cap premise. Optional-binder and native execution can retain it through the same actual construction code. No completed enclosing query or future callback law is needed in this design.

Once produced, `stored_probes`, the conditional cell law, and `hit_cleanup` compose to cap the exact warm smart-finish return. Empty is capped directly; the body case uses the derived old-body cap. This closes a guard-cap obligation without replacing the old winner by the current candidate.

## Validation and scope

`guard-probe-existing-public-1.log` passed nine imported full-signature and axiom pairs for the exact reusable endpoints and `MuStored`. No warning, error, truncation, or `sorryAx` occurs. The source-built obstruction kernel adds one successful pair. No canonical build was run by this reviewer, and no `.olean` was written.

No counterexample to the exact causal positive-depth readback target was found. The audit establishes a precise obstruction to the language-only shortcut and identifies the missing produced structural observation. General mixed native cap closure, its actual first-writer installation, general termination, and Haskell runtime correspondence remain separate obligations.
