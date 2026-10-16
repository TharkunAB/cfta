# Next current Merge profile producer

Reviewed: 2026-10-16 19:50 CEST. This is a read-only proof plan. No production file changed and no build ran for this review.

The remaining producer is the actual recursive `SourceCurrentMemoMergeGraph.Run`/`Call` profile theorem. The new Bounds, Cache, and Selection modules prove supporting facts. They do not prove this producer. Their comments state this boundary correctly.

## Smallest closed endpoint

Add a new generic profile-code module and a new profile producer module. Keep the three frozen foundations unchanged. The public `call_profile` should take the supplied current `Call`, initial `SemanticReady`, initial cost heap, physical `SourceCurrentMemoMergeEffects.Stored`, profile-cache `Stored`, `Available` input, and finite ordinary input domain. It should return the same actual heap/result/memo with physical `Effect`, final physical `Stored`, final profile `Stored`, output availability, and `MergeProfileCache.Certificate input output`. The input domain permits full guards and nonempty equality classes. It excludes Mu, explicit union, and reference nodes throughout. It needs no separate closedness or `ClassReady` premise.

For example, with namespaces abbreviated only in this proposal:

```lean
call_profile (actual : Graph.Call clear top input before memo output after saved)
  (semantic : SemanticReady before) (costs : CostHeap before)
  (physical : PhysicalStored before memo) (profiles : ProfileCache.Stored memo)
  (available : Available before input) (domain : Domain.Node input) :
  Effect before after ∧ PhysicalStored after saved ∧ ProfileCache.Stored saved ∧
    Available after output ∧ ProfileCache.Certificate input output
```

A wrapper can apply the certificate at any supplied input row, arity, and height limits. A finite wrapper must construct its own allocated call with `SourceCurrentAllocatedMergePhysical.call_complete` and then apply the producer. It must not take successful execution, a body certificate, or a desired returned profile as a public initial premise.

## Exact initial causal invariant

`MergeProfileCache.Certificate` quantifies over **every** original row limit, arity limit, and height limit (Cache:22). Its result uses `envelope rows bound` and retains height at most the captured original height. `Stored` applies that universal certificate to each entry's own complete original and result (Cache:27). One profile at one ambient limit does not establish this invariant.

Use this profile `Stored` together with physical `Stored` (MemoEffects:21). Physical storage supplies literal key coherence and resident captured records. `hit_certificate` then recovers equality of the captured original and the actual request through physical reference injectivity (Cache:66). Profile `Stored.domain` already derives the earlier conditional domain storage law (Cache:57). Do not add that older law as an independent initial premise.

The empty table satisfies both invariants. A warm initial table must have the certificates established for its earlier completed entries. The new induction must preserve this causal invariant at each actual completion. Arbitrary resident or semantically valid cache cells do not establish the profile invariant.

## Local body certificate to prove

Use `MergeCode.Certified` and its `bind_certified`/`map_certified` as the existing pattern (MergeCode:34,47,66). Its current request clause supplies only domain results. The new profile certificate must require an available finite ordinary request and pass the smaller actual Call's **full universal Certificate** to its continuation. Work and selection clauses must retain their literal actual outputs and heaps. Bind must check the suffix at the actual returned heap.

Prove all local branch certificates from the literal definitions. Do not leave `body_certified` or a recursive-result supplier as a public producer premise. Quantify the row/arity/height limits inside the proof or inside its postcondition. The candidate must have a universal Certificate before completion updates the memo.

- `small`: collect ordered child results, their unchanged child count, profiles, and child-relative height bounds. Rebuild the literal original guard. A membership-only map postcondition is insufficient to prove the arity count and maximum child height together.
- `column`: use `selected_profile` and `selected_inputs` for the exact selected list (Selection:18,36). These give membership and no increase in multiplicity. They do not give profiles for recursive outputs. `retained_column` excludes the explicit recursive-boundary branch for these ordinary inputs (Selection:47). Handle the selected singleton and selected empty list explicitly.
- Retained multi-value columns: bound the ordinary union by its selected input count. `column_inputs` bounds each original column by the source group length (Bounds:105). `ordinary_union` and `column_union` derive the actual union profile and height on the current coherent resident heap (Bounds:72,117). The recursive union input can need **rows squared**, even when every original child has only `rows` alternatives.
- `large`: collect the exact number of processed columns and their maximum child height. Apply the child Certificate at the squared row limit and the lower child-height ceiling. `column_envelope` embeds that result in the parent's envelope (Bounds:49). Use the row and height monotonicity lemmas when the actual union or selected list has a smaller bound. Prove the final literal Top-row constructor profile, including its actual cache-hit/sentinel behavior.
- `group` and `root`: retain actual ordered output lists and their profiles, lengths, and maximum height. `map_length`, `group_length`, and `groups_length` supply count bounds (Selection:63,74,89). `MergedSourceGrouping.groups_correct` supplies the exact flattened partition (Grouping:51). These counts must be combined with the new branch profile/height facts before the final `makeNode`. Canonicalization cannot increase the row count.
- `body`: split the actual input constructor and free-field test. The finite ordinary resident input has derived closedness from coherence, rather than a new free-field assumption. Empty and unchanged branches use `empty_certificate`/`self_certificate`. Keep the unsupported-input conditional nature of Certificate explicit; a vacuous Certificate alone is not a domain proof.

## Mutual actual graph induction

Adapt the structure of existing `Merge.run_domain`/`call_domain` (Merge:29,82), rather than a historical uncached worker or an assumed future result law.

1. Run pure/work/select retain the current profile table. Work grows the physical table through its actual effect. Selection uses its own actual finite receipt. Request invokes the smaller actual Call IH. Bind threads that exact intermediate heap and memo into the suffix.
2. A hit skips the body. Use `hit_certificate` with initial physical storage, semantic readiness, and request availability. Return the captured result and the unchanged heap and table.
3. A miss uses the smaller actual body Run IH plus the proved local body certificate to derive the candidate's full Certificate. Derive candidate domain and closedness from this Certificate and the input domain. Preserve the original's availability through the actual body effect.
4. At the body return, use the **current** physical and profile tables. Apply physical `stored_remember` and profile `winner_certificate` (Cache:87). A recursive call can have inserted the same key. The result is the winner reread after keep-first completion, not necessarily the candidate. A losing candidate's Certificate cannot establish the earlier winner's Certificate. `winner_existing_certificate` records that case (Cache:101).

`AllocatedMergeGraph.Run.graph` and `Call.graph` preserve the exact current heap, output, and completed memo (AllocatedGraph:158,175). Their extra equality-field allocation has a separate physical receipt. This supports a same-graph allocated wrapper. It does not substitute a cold uncached execution or identify heaps from different group orders. Existing physical completion and worker `call_sound`/`call_complete` then support finite and supplied-success wrappers at the same actual return.

## Current boundary and first next action

Projection profile/height and request bounds are complete in the current caller-resource endpoints. Required profile/height/positional length and request bounds are also complete (`CallerResources.required`:38 and `.projection`:61). These components must not be listed as missing producer work.

The first next proof is the local profile certificate with ordered map count and maximum-height posts. Then prove the mutual actual Run/Call producer and its exact winner storage invariant. Only then compose the allocated and literal worker wrappers.

General Merge profile production is still open at this review. Merge constructor/selection reservation bounds and cumulative Target, Shared, class, Local, Parent, and outer capacity are also open. A profile envelope alone bounds neither actual constructor requests nor total reservations. The completed sequential Merge graph still has the lazy-publication, pending-ancestor, concurrency, GHC, and runtime table/allocation boundaries stated in MemoGraph:4–13. This plan claims no whole-library or runtime correspondence result.
