# General recursive Merge profile producer

Status at 2026-10-16 19:50 CEST: three foundations are proved. The general memo-aware producer is not proved. No producer draft exists. No Empty-only production endpoint was added.

The frozen foundations are `SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds`, `MergeProfileCache`, and `MergeProfileSelection`. They prove the height-indexed row envelope, actual ordinary-union column bounds, exact-owner completed-table lifecycle, actual selection retention, and actual group multiplicity. Their 29 public declaration checks and six integration kernels pass. These facts do not prove a profile for recursive merge results.

The target is the actual allocated `Run`/`Call` in `SourceCurrentAllocatedMergeGraph.lean:133` and `:150`. Its `Run.graph` erasure preserves the exact returned constructor heap, output, and completed memo. It removes the separate equality-allocation instruction. It is a valid bridge to the existing memo-aware source code. It is not a bridge from a historical eager worker. The source grouping, threshold, columns, full small-row guard, and Top allocation are at `:49` through `:78`.

## Local Body certificate

Use the existing `SourceCurrentMemoMergeEffects.Certified` interpreter at `SourceCurrentMemoMergeEffects.lean:79`, with this stronger request contract:

```lean
ProfileContract input before result after :=
  SourceCurrentMemoMergeEffects.Contract input before result after ∧
  MergeProfileCache.Certificate input result
```

The necessary new local theorem has this form. Names below are proposed names, not existing declarations.

```lean
body_certified clear top input before semantic costs available rows arity profile :
  Certified ProfileContract clear (SourceCurrentMemoMergeGraph.body top input) before
    (fun after result =>
      SourceCurrentMemoMergeEffects.Contract input before result after ∧
      NodeShape (envelope rows (height input)) arity result ∧
      height result ≤ height input)
```

Here `profile : NodeShape rows arity input`. `semantic`, `costs`, and `available` concern only the initial heap. The request clause is a local induction contract. A public producer must discharge it by the actual mutually smaller `Call` proof. It must not retain an arbitrary callback that assumes the requested output profile.

Prove these local code facts in source order:

1. Add a contract-strengthening lemma for `Certified`. This lifts a physical body certificate to `ProfileContract` when its postcondition needs only the physical part. This is needed even when the enclosing input has no finite-ordinary profile: its body can still install profiled child entries.
2. Strengthen the ordered-map helper to retain output length and per-element height/profile facts. The existing physical `map_certified` at `SourceCurrentMemoMergeEffects.lean:131` does not retain cardinality. The actual graph count helpers in `MergeProfileSelection.lean:63` through `:98` supply the corresponding verification facts.
3. The body enters grouping only when its stored `free` field is empty. Coherent resident readback then supplies closed children for selection. A profile alone does not validate free-field metadata. For a small row, instantiate each child's universal certificate at its original profile and a bound no larger than `edgesHeight originalEdges`. Rebuild with the original full guard. Carry its exact child count.
4. For a large row, selection preserves the source child profiles and does not increase multiplicity (`MergeProfileSelection.lean:18`, `:36`). Its finite-ordinary retained inputs exclude `makeUnion` (`:47`). The actual ordinary union has input profile `rows * rows`, arity unchanged, and height no greater than the original edge maximum (`MergeProfileBounds.lean:117`). Its recursive result fits the parent envelope by `column_envelope` (`:49`). A singleton uses its unchanged profile.
5. Retain the actual column count, which is bounded by the first row's arity. The new Top field is a separate actual equality allocation in the allocated graph. It does not change the constructor profile proof.
6. For group/root code, retain the threshold output count and total original row count. Rebuild the final node from these exact ordered rows. Do not use one constant row limit for every recursive input: the column step needs the squared limit.

## Mutual Run and Call proof

Use actual graph induction, following the structure of `run_effects` at `SourceCurrentMemoMergeEffects.lean:339`. The Run motive must return physical effects, physical `Stored`, profile `Stored`, and the supplied local certified postcondition. The Call motive must return those invariants plus the physical contract and the universal `MergeProfileCache.Certificate input result`.

A hit uses physical readback and `MergeProfileCache.hit_certificate` (`MergeProfileCache.lean:66`). This identifies the complete stored owner with the candidate request. A hit must use the owner's certificate and return its exact stored result.

For a miss, first use the smaller actual body Run and the lifted physical certificate to derive its exact effects and both returned table invariants. To prove the candidate's universal certificate, introduce arbitrary `rows`, `arity`, and `bound` with an input profile and `height input ≤ bound`. Apply the same strictly smaller body Run induction hypothesis to the fixed-profile `body_certified` theorem above. Its actual result and state remain fixed. Weaken the result envelope from `height input` to `bound`. This proves the candidate certificate without assuming a parent or output language law.

Finish with `remember_stored` and `winner_certificate` at `MergeProfileCache.lean:47` and `:87`. Reread the actual current memo after the body. An earlier reentrant winner can differ from the candidate. Its stored certificate certifies that winner. Do not assign the losing candidate's profile to an earlier winner. The `winner_existing_certificate` theorem at `:101` and the invalid-candidate kernel test this case without a candidate certificate.

Only after this mutual producer closes should a public allocated profile theorem compose it with `Call.graph` and existing allocated effects. A finite endpoint can then reuse the current finite actual Call construction at `SourceCurrentAllocatedFiniteOrdinaryMerge.lean:116`. No future body/result certificate should remain in that endpoint.

## Boundaries

These foundations do not prove constructor reservation counts for Merge. They do not discharge cumulative Target, edit, class, or outer budgets. Comparison reads and equality allocations need their own resource accounting. The completed serial Merge graph retains its existing pending-publication and GHC forcing-order boundary. Current native intersection output-profile production is already proved in the previous checkpoint; it is not the missing step here.
