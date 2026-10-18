# Causal source comparison with the prior payload invariant

Reviewed on 2026-10-18 at 20:00 CEST. This is a read-only proof design. No Lean jobs or production edits were made.

The route is viable as a next proof target. I found no missing stronger-payload premise in its binder reduction. Keep `StoredMuRootContract.Correct` as a checked sufficient interface, but do not require it in the general source-law premise before trying this route. The proposed proof uses the prior `StoredMuProfileContract.Correct` plus an actual empty-table publication history. The source law and its chronological invariant producer remain unproved.

## Concrete source law

Use one fixed `reader` throughout structural induction. Let `P` be the existing `SourceCurrentStoredMuProfileContract.Correct`. A useful law for each source `expression` is:

```text
inputs : List (Sum Value Atom)
firstNames secondNames : Atom -> Reference
rhoFirst rhoSecond : Reference -> Profile
cutsFirst cutsSecond : Reference -> Bool

Aliases expression inputs firstNames secondNames
ScopedProfileInputs.Compatible expression inputs
  firstNames secondNames rhoFirst rhoSecond

(forall n, inl n in support expression inputs ->
  cutsFirst n = cutsSecond n)
(forall a, inr a in support expression inputs ->
  cutsFirst (firstNames a) = cutsSecond (secondNames a))

Context firstBefore (inputs.map (input firstNames))
Context secondBefore (inputs.map (input secondNames))
build expression ... firstBefore  = done first firstAfter
build expression ... secondBefore = done second secondAfter
Grows firstAfter reader
Grows secondAfter reader
Heap P reader
History empty reader

=> Equivalent (deleted cutsFirst first rhoFirst)
              (deleted cutsSecond second rhoSecond)
```

`Context` is the joint `ConstrainedCapSourceHistory.Context`. `History` is `NativeMuPublication.History`. The two calls can have separate historical entry and return states. Neither entry is required to equal `reader`. No `Ready reader`, future result law, warm replay, whole lexical availability at the reader, or `RootContract` is part of this proposed law. The live cut condition is necessary even for `.var 0`; equal assigned profiles alone do not imply equal cuts.

Keep exact bare-reference parity as a companion structural fact. It need not be a second semantic induction premise: `UsedBinderOutputTags.bare` and `scoped_bare` already provide it from actual calls, contexts, and the appropriate live alias tests. `NativeNormalizationInputs.actual_free` identifies a live source label for any bare result. These facts also handle the standalone-reference exception when a callback filter is reconstructed.

## Why one reader is sufficient

For any nested binder call, actual constructor growth gives `Grows nestedAfter firstAfter` or its second-call counterpart. Composition gives `Grows nestedAfter reader`. Project `Heap P reader` backward by sending each exact stored record through `growth.nodeRecords`. This gives the old heap premise at the nested return state required by `NativeBinderProfile.build_profile`.

The same exact stored record is present in `reader`, so `NativeNormalizedComparisonExecution.history_unused` applies there. Its conclusion is state independent. There is no need to infer `History empty nestedAfter` backward from the final history. This avoids the internal-history problem. The proof never changes the common reader or transports an observation relation.

The source induction recurses only on the current expression's strict source children. It does not recurse on an earlier writer's expression. An earlier selected writer can have larger syntax. Its old `P` law is already in the common heap; its exact unused readback comes from the common causal history.

## Binder cases

Both executions expose their actual Depth and ordinary callbacks through `NativeBinderExecution.decompose`. `NativeNormalizedComparison.probes_same`, lines 295–314, gives the same `usesLocal` decision from the same symbolic source inputs. Actual free-name support gives matching closed/open status for the two whole results. This last fact is needed for the closed-Mu shortcut in `NativeBinderProfile.build_profile`.

For a retained Mu, `deleted` ignores the cut predicate at that root. Apply the actual decomposition and selected old payload law used in `NativeBinderProfile.build_profile`. Choose one marker outside both finite assigned-leaf supports. Use the underlying `StoredMuFinishProfile.finish_profile` with that explicit common marker; `build_profile` alone returns an independently chosen existential marker. Its open branch reduces to erasure of the common marker from the current ordinary probe profile. Its closed branch is opaque. Compare the two current ordinary probes through strict source-body induction, with the same local marker profile and their actual root filters. The old payload law is used only unfiltered in this case. Do not push the outer cuts into a retained Mu body.

For smart-unused construction, the record in `reader` and `history_unused`, lines 417–423, give the literal equation:

```text
finished value = eraseSelf ordinaryName currentOrdinary
```

The current ordinary callback is an actual execution of the strict source body. `NativeCallbackErasure.callback_result`, lines 51–66, derives availability of this erased value and absence of its ordinary name from the complete free set. Therefore changing the profile assignment at that local name does not change its deletion observation. Choose a common Empty local profile, then use strict source-body induction. No historical writer-body/current-probe root equality is required.

The main missing algebraic helper is the following normal, available, actual-filter law. It is not a desired parent output law:

```text
deleted cuts (eraseSelf own (run (withoutSelfReference own raw) state).1) rho
  Equivalent
deleted (fun n => cuts n || (n == own)) raw rho
```

It follows by the actual root cases and `StoredRootDeletionConstruction.makeUnion`. The standalone-own case becomes Empty on both sides. A root Mu remains atomic on both sides. After this helper, local absence permits the Empty shadow, and the strict-body IH uses the combined outer/local cuts. The retained branch needs only the existing singleton-filter bridge, with exact bare parity for its exception.

Node and union source cases need the actual indexed child schedules. Node uses the uncut instance of the child law at original live rows. Original dead rows remain dead under every assignment because they contain an actual Empty child. Union uses the member law with the current cuts and the new actual `makeUnion` deletion theorem. These steps do not need a hereditary finite domain or a writer-syntax rank.

## Chronological old-P producer

The source law assumes only `Heap P reader`; it does not produce that heap for arbitrary future executions. Produce it separately by induction on actual `NativeMuIssuedHistory.Path`, with the stronger induction statement:

```text
forall prefix : History empty before,
  Heap P before -> Heap P after
```

For a publication constructor, use the actual child paths and explicit prefix composition:

1. `depthPrefix = prefix.trans depthPath.forget.history`.
2. `cutPrefix = depthPrefix.trans ordinaryPath.forget.history`.
3. `allocatedPrefix = cutPrefix.trans reserveHistory`, where reservation adds no Mu.
4. `bodyPrefix = allocatedPrefix.trans bodyPath.forget.history`.

Run the nested path IHs in that order. They provide `Heap P event.afterBody` before the current candidate is installed. `bodyPrefix` provides `History empty event.afterBody`. Apply the proposed source law to the event's raw ordinary and reserved builds, with `reader = event.afterBody`. `NativeMuPublicationCallbacks.raw_callbacks`, lines 47–97, supplies both actual builds, entry contexts, filters, and raw-return growth into that reader. Actual publication freshness aligns local shadows and local cuts. Exact bare parity handles the two callback filters. Their unfiltered profiles then give `P` for the candidate under every outer assignment and common local profile.

Finally use `PublicationHeapInduction.complete`: either the already proved old winner remains, or the proved candidate is installed. This argument never assumes the current candidate's law in order to prove it.

The existing `PublicationHeapInduction.path_heap`, lines 57–74, exposes earlier heap facts but omits the actual prefix and child-path arguments from its candidate callback. Do not obtain the prefix by reversing a history or by projecting from `Grows`. A new prefix-carrying fold, or direct induction on `Path`, is needed. `Path.forget`, `GrowthHistory.Path.history`, and the actual reserve step supply every required forward segment.

## Remaining hard steps and scope

The next main proof has four concrete parts: the erased-filter deletion helper; the fixed-reader structural source law with live cut extensions; the retained/open-Mu ordinary-probe and shared-fresh-marker comparison; and the explicit prefix-carrying chronological producer. Existing physical unused readback removes the need for a stronger stored root heap in this route. It does not complete those four proofs.

No counterexample to this causal target was found. The earlier artificial cache obstruction remains valid because it has no actual empty-table history. No arbitrary heap is upgraded from coherence or old `P` alone. This route concerns root profiles and actual source construction. It does not prove all-depth reader observation congruence, general outer completion, convergence, or Haskell correspondence.

## Central source pins

| Source in `lean/MicroCFTA/` | SHA-256 |
| --- | --- |
| `SourceCurrentNativeMuIssuedHistory.lean` | `1d3d4fcd733ed325287bbfb288b70df88476b3989657b056dd3819abf4079563` |
| `SourceCurrentNativeMuGrowthHistory.lean` | `98c08f9029a262a632d56d67e3038aadecccd9b5aa4fa112dd8bde3b132a9c0a` |
| `SourceCurrentPublicationHeapInduction.lean` | `690392065b04a6b3e30a22279b058b8b88214d0ffa985e26d127f44ac3f6df9a` |
| `SourceCurrentNativeNormalizedComparisonExecution.lean` | `9d2f9e64c62396b76e32c76428369188fc09371c1b19e100f8c0ca79b80e1a00` |
| `SourceCurrentNativeCallbackErasure.lean` | `33a654079ed23f616c2935b5942d9f789d1b31f2bfaeaecc7ee78a9cdd6c8b60` |
| `SourceCurrentNativeBinderProfile.lean` | `89b5643f3f51e08c441ebc4e014243a24b73abac0efc1086678976c4dfd566e2` |
| `SourceCurrentStoredRootDeletionConstruction.lean` | `4f5ab3e64000ec9bb54cb95e17a03f5634fbe803eead98af89dcbd42c7c58de5` |
| `SourceCurrentStoredMuRootContract.lean` | `6d0ab051177b85cd726a884a4b084b6a880084dc095bf3ee4f29197c6d641ec5` |
