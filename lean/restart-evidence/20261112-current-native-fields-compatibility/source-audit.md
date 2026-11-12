# Current native Type fields, caller and startup

Base: 85cd534cf7c43c3eef4d84b2b2cc90fce1032dae. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, including PR210/211.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisCurrentCallerInitialization: 80 lines; 1 laws; SHA256 8e65a4f4015d984b5beeba739d8ddbff7c91961139099fa5ceddaed1045c9857.
  - MicroCFTA.SourceSynthesisCurrentCallerInitialization.accepted
- SourceSynthesisCurrentInitialModelWork: 119 lines; 1 laws; SHA256 244b4ede1500b8f924d2981e4d030373ea9572d2865f63aadbf2e3e86ff73601.
  - MicroCFTA.SourceSynthesisCurrentInitialModelWork.accepted
- SourceSynthesisProgramTypeFieldConstruction: 320 lines; 2 laws; SHA256 3ff2638deefde91440e5a5505dbdb25fe741e3bfbb5f0df17bf6da593bc3edf2.
  - MicroCFTA.SourceSynthesisProgramTypeFieldConstruction.build_program_fields
  - MicroCFTA.SourceSynthesisProgramTypeFieldConstruction.current_root_fields
- SourcePruningEnumerationSharedPreparedChildPolicy: 124 lines; 4 laws; SHA256 16b4b297c900ffe36686c5e1de3dd707f4083b9391b12b20456cd41dedda7d18.
  - MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild_shallow
  - MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy.preparation_readback
  - MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy.runEager_preparation_readback
  - MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy.failed

## Exact contracts

CurrentCallerInitialization.accepted invokes closed_complete once. It derives
its actual native build, equality preparation Receipt/cache, conjunction
Fields, full Context/inventory/caller/modeled globals, Facts, Available,
ProgramValue, growth/issued extension and full physical guard-origin Heap.
It retains the same inherited live value, equality readiness, root closedness
and Original. It assumes current source success and valid initial equality
cache. It does not assume a future build, Context, Fields, worker or model.

ProgramTypeFieldConstruction.build_program_fields threads an existing
ProgramSyntax certificate and Allowed for every ordered Type operand through
one actual generic build. Its mutually dependent list traversal follows the
actual first/tail buildMany endpoints, predecessor Context and Mu store.
The result retains the complete post-build Mu store and existing ValueFields
on the SAME literal Program value. current_root_fields derives all static
premises from current actual root success and an actual empty-context build.
Its Origin uses the once-encoded library. It covers all avoid rules. It does
not add an evaluator, Program typing hierarchy, second build or annotation
supplier. Derived guard origins alone still do not imply literal physical
projectability.

CurrentInitialModelWork.accepted calls the current caller initializer once
and the generic raw-value startup producer once. It retains the COMPLETE
initializer tuple. It returns the same encoded/decoded handle, Packet,
canonical core, exact initial slot, suspended bound, waiting correctness,
candidate expansion, graph carrier and reference receipts. With empty
pending metadata, EACH term accepted by that same raw value retains its
Program Projection/toProgram and requested component count, an actual root
assignment, satisfaction, pending refutation and assignment origins. For
N = NumberedTerms.size term, pendingSize is exactly N and initial work is
(N+1)*N + (if recursiveBoundary value then 0 else 1).
N measures the complete annotated term. It is not Program.components.
This is cold initialization before a pruning worker. It assumes an accepted
term; source success can have an empty language. Modeled empty initial globals
do not assert that Haskell process-global caches reset.

SharedPreparedChildPolicy.runWithChild performs exactly one existing
SelectedPreparation.run. It retains every terminal/opaque/failure case and
changes only the ordinary branch child visitor. runEager uses the already
checked eagerChild operation. runWithChild_shallow is equality of the ENTIRE
Preparation and Option Fold pair. preparation_readback and eager readback
retain the exact same actual preparation; failed retains the exact physical
fault heap and entry with no hook. The complete common recursive driver is
not wired by this module. Existing finish can drop processed receipts on a
complete driver result; no stronger whole-trace output statement is made.

## Checks and scope

All four strict source packets pass. Full Audit passes: 5818 live modules,
five affected, 4815 imports, 93965 axiom reports. All five portable checks
pass, including the aggregate checker from /tmp. All 261039 previous Audit
bytes remain after four imports. The source/audit frontier pins are exact.
Effective memory.max and memory.high are 4294967296; memory.swap.max is zero.
Runs use one Lean thread and the repository Lake cache. No binary archive is
copied. The checks establish these manually specified Lean source models;
they do not certify a Haskell compiler, extraction or runtime correspondence.

Current checked hereditary-worker completion and recursive policy wiring are
NEXT drafts. The frozen worker audit below specifies a single current
initializer/one generic rank producer and exact computed Room. That audit is
not a checked endpoint theorem. Neither fixed-width capacity nor whole
enumeration is discharged. Source reverse soundness, default reduction/refold,
weights, source order/multiplicity/lazy demand, both inverses, original-input
work/depth, full guards/signed/Word/Int/errors and refinement/training remain.
Default synthesis does not call boundDepth. Prior proofs and counters remain.

## Haskell and external ownership

No Haskell source, Cabal file, production repair or new runtime defect is
introduced. The previous source-closure and current-admission packets retain
PR210/211 source pins and the focused Nix/GMP validation: fourmolu passes;
Data.CFTA.Gen.Synthesis has 16 examples and zero failures. That check is not
the full Haskell suite, corpus or benchmark. Historical negative packets remain
source-pinned. Curried reserved markers, raw generated-variable admission,
and the Liquid synthesis duplicate-reader review remain separately owned.
Liquid Haskell results do not automatically enter Lean or certify execution.

## Frozen next worker audit

The following read-only audit is retained as an unverified implementation
plan. It does not add a public proof or change the checked source hashes.

# Current checked shared worker

2026-11-12 16:11 CET. Read-only audit. No compiler, source, repository, Git, Haskell, root-doc, or evidence changes.

## Result

No additional source hypothesis is required for the current cold checked worker. The existing current caller and whole ValueFields observers supply the same inputs as the historical producer. Every other initial rank or hereditary condition has a public generic constructor law or an empty-table proof. The computed Room condition remains explicit and conditional on the actual derived heap/profile. It is not proved for native fixed-width execution.

Use ONE CurrentCallerInitialization.accepted call and preserve its complete returned tuple. Observe that SAME build with ProgramTypeFieldConstruction.current_root_fields. Instantiate every Type-indexed library parameter with `E lib := CurrentSourceGuards.encodedLibrary lib`. Do not pass raw lib to a Type-origin theorem after obtaining fields under E lib. No equality with historical firstOrderRaw or historical typesOf is needed.

References below use `lean/MicroCFTA/`. Abbreviated Synthesis module names have the prefix SourceSynthesis. `I`, `C`, `G`, `emptyValue`, `operations`, and `checked` are PartialInitialization.inventory, caller, globals, emptyValue, operations, and checked. `Symbol` is Label FullSyntax.Formula. `Guard` is the existing source Constraint. `Origin` is NativeTypeTrace.Origin. `literal` and `ordinarySymbols` are the existing Label adapter. The formulas/solver and three equality instances match OriginalCheckedHereditarySharedCompletion.

## Cold Type and shared readiness

CurrentCallerInitialization.accepted:31 derives one build, preparation receipt, conjunction fields, Context, Facts, availability, ProgramValue, growth, issued-key extension, full literal guard-origin heap, inherited empty-value identity/readiness, closedness, and Original value. Preserve all of these fields. In particular preserve the SAME proof-indexed I, returned cache, caller C, and G.

ProgramTypeFieldConstruction.current_root_fields on that SAME build returns MuStored (Origin (E lib)) heap and complete ValueFields at value. These are observers of the existing endpoint, not another build producer.

For `before := C width cache heap`, construct the exact checked TypeReady record, indexed by E lib:

```lean
have typed : NativeTypeClosedRequests.Ready (E lib) before.checked :=
  ⟨context.ready.good,
   SourceEqualityRequiredSemanticCache.constructed (ordinarySymbols expression) value heap built,
   SourceCurrentAllocatedNativeScopeCache.initial_scoped width ⟨heap, Cache.emptyState⟩,
   SourceRecursiveIntersectionNative.idle_initial _,
   SourceCurrentHereditaryNativeUniversalStore.initial (Origin (E lib))
     ⟨heap, Cache.emptyState⟩ (operations cache) sourceMuStored⟩
```

Relevant APIs: NativeTypeClosedRequests.Ready:32-37; HereditaryNativeUniversalStore.initial:30; PartialInitialization.checked:36 and caller:40. These initial states are the SAME cold state by their definitions. SourceMuStored is the just-derived post-store at the actual built heap. It is not a supplied future store. The existing historical cold_ready wrapper at NativeTypeClosedRequests:41 is not needed.

Derive CostHeap from InternedFreshOrdinaryCosts.closed_heap at the SAME built equation. Then use NativeTypeSharedState.initial:37 with the above typed record, CostHeap, CurrentMemoMergeEffects.stored_empty heap, and CurrentHereditaryMerge.stored_empty (Origin (E lib)). The result is SharedReady (E lib) (initialShared before.checked before.merge). Empty target slots discharge their own pointwise obligation. No future TypeReady or target classification premise is added.

## Rank prerequisites are all current initialization facts

| Required fact | Exact source of the same-state fact |
| --- | --- |
| Context and initial inventory/global memos | CurrentCallerInitialization.accepted; I expression/value/heap/built and G are retained |
| Frame | SourceCurrentConstructedOuterInitial.frame, as in OriginalSharedRankCompletion:73-78, using the SAME build/context.ready |
| Fits of the numeric seed | nodes/edges/domain reflexive bounds and InternedValueMassHeap.initial heap facts |
| Initial finite guard-list annotation heap | SourceCurrentConjunctionGuardUniverse.initial heap facts |
| Ready inherited empty payload and closed available value | SAME caller identity/readiness/closedness tuple; rewrite emptyValue with that identity |
| UnionNormal heap | SourceCurrentRequiredUnionNormal.build on SAME source build and empty initial UnionNormal |
| Positive native support | both initial native tables are empty; FlatMemoThunk.empty_valid |
| Causal Mu publication | SourceCurrentNativeMuPublication.closed_history on SAME source build |
| Plain stored merge obligations | SourceCurrentConstrainedCapMemoMerge.stored_empty |
| Positive merge support | SourceCurrentMergePositivePosition.support_empty:32 |
| Physical parent writers | SourceCurrentSharedResourceParentWriters.initial:94 on actual initial checked/merge/fourth |
| Closed prior returned nodes | SourceCurrentSharedOuterClosedInputs.initial:50 |
| Initial node idle | initial nodeResults.cells has no evaluating cell; cases the impossible lookup |
| Initial edge idle | SourceCurrentSharedOuterEdgeIdle.initial:38 |
| Type guard profile heap | SourceCurrentConstrainedCapGuardExecution.closed_heap:341 at Origin (E lib), rewritten by SAME built |
| Hereditary outer memo history | HereditaryClosedMemo.initial:62 at E lib/literal and SAME initial checked/merge/fourth |

The Type GuardHeap row is a causal Mu/profile invariant. It is not the physical statement that every Program guard is a Type-origin guard. The initializer separately retains the complete physical annotation heap under Derived (alphabet (E lib)) top conjoin. Preserve that physical fact and the worker's forecast guard-list annotation heap independently. No all-Program-guards-in-Type-pool premise is valid or needed.

PlainMu has already supplied the checked current Type-field/prefix store route. The new whole ValueFields observer also threads the actual current store from empty. Do not impose PlainMu again as a public worker premise. There is no additional source support, unique-name, avoid, guard, closed-store, or idle hypothesis to request.

## Exact computed capacity and completion packet

Keep the existing heap-only OriginalSharedRankCompletion.seed:41. Its name is historical, but its definition is generic in heap. It stores the initial physical guard list, node/edge counters, zero native domain count, and actual value-mass bound. It does not claim a native size bound from requested Program components.

Inside the returned initializer witnesses define exactly:

```lean
let request : NodeRequest := ⟨emptyValue cache, value⟩
let output := SourceCurrentSharedOuterRankEnvelope.envelope budget
  (SourceCurrentPositiveQuotientCount.count (request.inherited.payload.getD []) value)
  (InternedValueMass.value value) (OriginalSharedRankCompletion.seed heap)
let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (C (bits + 2) cache heap)
let need := SourceCurrentSharedOuterInitialFuel.phaseNeed budget first
  (OriginalSharedRankCompletion.seed heap)
Room bits (SourceCurrentInitialSelectionForecast.cover [output.2.2.2]
  (SourceCurrentSharedOuterInitialPrefix.forecast budget first
    (OriginalSharedRankCompletion.seed heap)).2) → _
```

Call SharedOuterRankAdequacy.initial_node_call:177 ONCE with this SAME seed/caller/request, the current facts above, and all nine lower bounds set to need. It PRODUCES one result/after and stable successful equations for every fuel ≥ output.1. It takes no future successful worker as input. The Room branch belongs AFTER the actual build/preparation witnesses. A separate guessed future profile, successful run, or Room supplier must not appear in the public header.

Use the base equation `done output.1 (Nat.le_refl _)`. Combined Room gives base root Room through room.mono cover_ge. HereditarySharedOuterTraversal.nodeCall_fields:592 applies directly at E lib and literal, with the SAME Context/Frame/Fits/known, initial SharedReady, Type GuardHeap, History, inherited readiness, availability, closedness, and Or.inr sourceValueFields. It returns the SAME actual endpoint's one inventory `next`, full memo bundle `final`, graph, canonical NodeCallReads from G, Post, Frame, Fits, forecast physical guard-list heap, availability, immutable NodeLaw, SharedReady, Type GuardHeap, History, closedness, and NodeFields. NodeFields.program sourceValueFields appends complete returned ValueFields.

Checked ranges need no new native proof. Use InitialLiteralRanges.node_call:308 at the base schedule; ChecksFromRanges.node_call:283 derives Checks for that SAME graph/base equation; RangesFromChecks.node_call:273 derives ranges for EVERY larger stable actual run. Retain one graph/read/Post bundle from the BASE schedule. No larger schedule Room condition is required. Stable outer-fuel endpoints do not assert identical intermediate schedules.

## Exact next wrapper header

The smallest complete producer is `SourceSynthesisCurrentCheckedHereditarySharedCompletion.accepted`. Its inputs are:

```lean
(lib : Library) (query : Query) (signed : Int) (expression : Expression)
(returned : CurrentConstruction.firstOrderRaw lib query signed = .ok expression)
(bits budget : Nat)
(formulas : SourceGuards.Formulas FullSyntax.Formula)
(solver : SourceGuards.Entailment FullSyntax.Formula)
```

Its existential prefix retains the ENTIRE CurrentCallerInitialization.accepted tuple at width bits+2, initial Cache.emptyState/empty_valid. Append SAME initial MuStored, ValueFields, SharedReady, Type GuardHeap, and History if these initial certificates are exposed; derive them internally otherwise. A new opaque packet type is unnecessary. After that prefix use the exact computed Room implication above. Its conclusion is the following existing full endpoint tuple, with only the Type library index changed to E lib:

```lean
∃ result after,
  Ranges.nodeCall output.1 need need need need need need need need need budget request before ∧
  (∀ fuel, output.1 ≤ fuel →
    nodeCall fuel need need need need need need need need need budget request before = .done result after) ∧
  (∀ fuel, output.1 ≤ fuel →
    Ranges.nodeCall fuel need need need need need need need need need budget request before) ∧
  ∃ next final, ∃ graph : NodeCall budget request before result after,
    Checks (nodeCallTrace graph) ∧ NodeCallReads formulas solver graph G final ∧
    Post formulas solver next before after final ∧ Frame formulas solver next after.checked ∧
    Fits (forecast budget first seed).2 after.checked ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (forecast budget first seed).1)
      after.checked.native.machine.heap ∧
    Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result ∧
    SharedReady (E lib) (initialShared after.checked after.merge) ∧
    GuardHeap (Origin (E lib)) after.checked.native.machine.heap ∧ History (E lib) literal after ∧
    result.free = [] ∧ NodeFields (E lib) literal request result ∧
    ValueFields (Origin (E lib)) literal result
```

Here Ranges, NodeCall/Reads/Checks, Post, Frame/Fits, SharedReady, GuardHeap, History, and NodeFields are EXACTLY the modules and types used by OriginalCheckedHereditarySharedCompletion.accepted:48-88. `before` is the SAME C (bits+2) cache heap, and `seed` is the SAME seed heap. Do not replace next/final by a projected query memo or leave the inventory implicit behind a future supplier.

This is executable proof composition now: call the current initializer once; observe its build once for the two Type-field outputs; form cold readiness/empty-table facts; invoke rank adequacy once; observe that actual base return with nodeCall_fields; attach checks and stable ranges. No new recursive worker, source interpreter, semantic assignment, or model is required. If a smaller first source file is preferred, extract only the same-build cold TypeReady/SharedReady observer; it has no missing mathematical premise and is a subset of this producer.

An accepted-term Program-count corollary is also generic after this cut. Use current_root_structure.2 and OriginalProgramTermSize.build_accepted on the SAME build, then transport accepted result terms through the returned NodeLaw. It need not be included in the first checked hereditary module. Startup at the worker result is a later composition with this exact Context/Post endpoint. CurrentInitialModelWork concerns raw cold startup and must not be substituted for it.

The remaining limits are actual computed Room at fixed native width, complete enumeration and earlier-sibling completion, generated rank/guard bounds, default eager-order behavior, and Haskell extraction/correspondence. This conditional worker result does not close those limits.
