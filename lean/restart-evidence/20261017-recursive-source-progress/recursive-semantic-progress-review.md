# Recursive native progress audit

Status: read-only production audit. Date: 2026-10-17 00:33 CEST.

The current allocated native executor already has general closed recursive completion, conditional on reached machine-key bounds. This result is broader than the finite ordinary domain. It allows original Mu, union, and bound-reference payloads. The remaining native progress premise is `SourceCurrentAllocatedNativeRequestBounds.WordRanges`. It is not a supplied successful execution, a completed physical trace, or a smaller-body completion callback.

## Strongest current endpoints

- `SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete`, lines 535–557, handles a warm full checked state. It takes `Good before`, `Idle before.native`, two available closed original operands, and current `WordRanges` for `requestNode emptyDomain left right`. It constructs a physical `Receipt`, a finite bound, the actual result and full returned checked state, and final `Idle`. `Receipt.done` at line 107 derives the literal `SourceEqualityNativeDemand.execute (fuel+1) ... = .done ...`. Receipt fields at lines 90–99 retain final `Good`, machine `Extension`, heap `Keeps`, and equality-operation `Grows`. This endpoint does not claim semantic correctness of arbitrary warm completed memo results.
- `SourceCurrentAllocatedNativeColdClosedExact.cold_complete`, lines 37–70, is the strongest convenient closed cold semantic endpoint. It takes formulas/solver, the actual constructor/domain machine and equality-operation state, `Good` for cold native tables, `SemanticReady heap`, original/available/closed left and right, and the same current `WordRanges`. It derives the input model and rank model internally. It returns one actual contextual receipt, scoped final memo tables, final `Idle`, a closed result, and exact intersection language for every ambient environment and term. Its two independent completion inductions are aligned by whole-checked-state determinism, not by an assumed result equation.
- For a warm semantic cache, `SourceCurrentAllocatedNativeContextualCompletion.initial_complete`, line 606, additionally needs the existing contextual-cache invariant and input model/ranking, plus semantic heap readiness. Physical `Good` alone does not supply that warm result-language invariant.

`Good` is explicit representation input, not mere table validity. Its four fields at `SourceCurrentAllocatedNativePhysicalCompletion.lean:27` are physical native validity, `SourceEqualityRequiredCache.Ready`, equality-operation validity, and loaded fields. `Ready` at `SourceEqualityRequiredCache.lean:19` contains semantic heap, coverage, and decoded depth invariants. `SemanticReady` at `SourceEqualityRequiredSemanticCache.lean:18` also contains guarded and budget probe heaps.

The public `Original` hypotheses are derivable from coherent availability and empty free lists by `SourceRecursiveIntersectionOriginalOutput.closed_original`, line 91. The imported integration kernel `current_query_done` makes this derivation explicit before it invokes current physical completion. Thus there is no finite-ordinary restriction hidden in `Original`.

## The semantic completion premise is discharged

`IntersectRequiredFuel.lean:15` defines `Completes view call` as the existence of a successful semantic schedule bound and result. `requiredFuel`, line 43, chooses its least successful bound. This definition alone would not prove termination.

The independent chain does prove the needed initial `Completes`:

1. `SourceRecursiveIntersectionInputExact.source_schedule_total`, line 100, constructs a stable successful semantic run and exact language from actual source `Facts`, original available operands, and their closedness. `schedule_total`, line 85, supplies the analogous codec-input theorem.
2. `SourceRecursiveIntersectionRequestProgress.initial_complete`, line 77, obtains initial empty-domain `Completes` from that totality theorem. `physical_child_requiredFuel`, line 33, derives strictly smaller semantic bounds for actual selected recursive branches. `entered_requiredFuel`, line 53, retains the exact measure through actual canonical domain allocation.
3. In the older executor, `NativeBodyProgress.BodiesBelow`, line 17, is a temporary induction interface. The explicit `bodies` and continuation hypotheses in `NativeNodeProgress.node_terminal:17`, `NativeEdgeProgress.edge_terminal:17`, and `NativeCodeProgress.code_terminal_of_bodies:18` are not the final residual premises. `NativeFiniteObservation.code_terminal:19` constructs both `BodiesBelow` fields by strong induction on `requiredFuel`.
4. The current physical executor repeats this proof at its actual checked controls. `SourceCurrentAllocatedNativePhysicalTraceCompletion.all_bodies`, line 447, closes the internal smaller-body obligations. Public `code_complete:472`, `node_complete:487`, `edge_complete:502`, and `request_complete:517` lead to `initial_complete:535`. The edge body uses actual allocated equality conjoin and rejection branches. It does not substitute the older eager `compileEdge` execution.

The requested demand lemmas are consistent with this chain. `NativeDemandProgress.node_busy_impossible:44` and `edge_busy_impossible:70` need safe exact key readback, a complete current request strictly below the active stored owners, and `ActiveAbove`. They do not claim that an arbitrary busy cache is impossible. Absent publication is excluded separately at lines 16 and 30.

## Best current initial syntax family

There is no need to restrict source construction to the example `Mu x.(base | step x)` or to binder-free syntax. `InternedFreshOrdinaryClosedCompletion.closed_complete`, line 50, constructs a complete actual value and heap for every repaired literal `Syntax` expression under the empty environment. It permits nested binders, unions, and references handled by that construction model.

`SourceCurrentAllocatedNativeOriginalHistory.constructed`, line 126, then derives current cold `Good`, `SemanticReady`, availability, closedness, and `Original` for the actual constructed root from a valid covered field-allocation history. `SourceCurrentConjunctionClassHistoryEntry.constructed:32` additionally packages scan readiness. The imported kernel `constructed_current_inputs` composes closed construction with that current allocation-history endpoint. It supplies neither native execution nor a future result law.

For a nontrivial two-operand query, both chosen records must be available and closed in one common source heap. A root construction guarantees these facts for its root; it does not make every nested child closed. Binder bodies can be open. The completion theorem accepts any two records for which the initial facts hold. This is the honest general recursive native family, conditional on word safety. It is not yet general recursive constrained outer reduction or repeated fixed-point convergence.

## Exact residual machine premise

`SourceCurrentAllocatedNativeRequestBounds.WordRanges`, line 134, is:

```lean
∀ fuel next after, Steps fuel control state next after → Words width next
```

`Words`, line 126, checks only reached node and edge requests. It quantifies over every finite yielded checked prefix, including prefixes that never complete. Node checks are required when the optional source key is present. Edge checks are unconditional at a reached edge instruction.

`SourceRecursiveIntersectionMemo.KeySafe:21` requires positive width, `domain.identity < 2^(width-1)`, and safe complete tagged operand keys. `SourceRecursiveIntersectionEdgeMemo.KeySafe:20` requires the same signed-domain bound and each raw edge identity below `2^width`. Reference tagging has its own reserved-sentinel margin: `IntersectionFlatMemoKey.safe_range:122` gives `Safe (bits+2) (.ref identity) ↔ identity+1 < 2^bits`. An unsigned node-counter bound alone must not silently erase that margin.

Existing `SourceCurrentAllocatedFiniteOrdinaryWords.node:29` and `node_of_domain:42` derive these reached checks for the Mu/union/reference-free domain from original operand key bounds. `SourceCurrentAllocatedFiniteOrdinaryBoundedFinite.finite:29` composes this with native completion. They do not yet remove `WordRanges` for general recursive inputs.

No output-interner capacity or supplied completed `Trace` is a separate premise of the general native completion theorem. Constructor heaps are unbounded in this model. The unresolved numeric check concerns request keys, especially new canonical domain identities introduced by recursive entry. A quantitative constructor budget would be useful for broader caller composition, but it is a stronger additional result.

## Concrete next proof API

A useful next additive module is a recursive request-origin and domain-reservation theorem, not another termination callback:

```lean
-- Proposed, not proved by this audit.
recursive_node_words
  (before : SourceEqualityNativeDemand.State (bits + 2))
  (good : Good before)
  (left right : Value Symbol Guard)
  (leftAvailable : Available before.native.machine.heap left)
  (rightAvailable : Available before.native.machine.heap right)
  (leftClosed : left.free = []) (rightClosed : right.free = [])
  (originalOperandKeys : initial original inputs fit the tagged-key layout)
  (originalEdgeKeys : initial original rows fit the raw-edge layout)
  (domainRoom : initial domain supply + computedDomainBudget ≤ 2^(bits+1))
  : WordRanges (.code (requestNode emptyDomain left right)) before
```

`computedDomainBudget` must be defined from the actual finite original input carrier and proved sufficient. It must not be a supplied list of future reached keys. A conservative candidate counts all canonical domains whose free-name set is a subset of the original binder identities and whose seen set is a subset of possible original operand pairs. `SourceRecursiveIntersectionDomain.Typed:22` fixes each free entry to `name ↦ NodeRef.mu name`; `extend:30`, `extend_canonical:62`, and `extend_typed:101` ground this finite representation. Thus a powerset bound such as `2^(binderCount+pairCount)` is a candidate, subject to a complete prefix proof and initial warm-cache supply accounting. It is a design obligation, not an established bound here.

The proof must follow arbitrary current checked `Steps` before completion. It must extend current source-origin preservation through `.enter`, `.read`, `.optionalBinder`, driver frames, and exact warm-owner lookup. Actual readback must identify an owner with its original request at safe demands. It must prove new canonical domain identities fit from the initial supply and the finite set of new original-domain keys. An initial-only theorem of this shape would compose directly with the already proved current `initial_complete` and cold exact-language endpoint.

The exact remaining proof obligations are: preserve the original source operand/row carrier through every finite current prefix; preserve Typed/canonical domain subsets through enter and reset; prove an injective finite encoding of those canonical subset keys; bound actual new domain allocations even when the initial warm domain cache contains unrelated keys; and retain physical Good and exact finish-owner frames at the same checked states. The next proof must establish safe keys before it uses physical cache exact readback. It must not obtain them from a completed physical trace that already records the desired checks.

The fixed original carrier belongs to one native query. The outer reducer can construct new records and inherited constraints and can issue later queries on those outputs. This audit supplies no fixed carrier for the full recursive outer caller.

## Measures and counterexamples to simpler candidates

The actual semantic totality measure is the lexicographic pair at `IntersectTotal.lean:444`: closed-root size sum, then the local measure. `IntersectProgress.measure:56` uses remaining unseen original pairs, local input weight, and the canonical swap phase. `IntersectTotal.reset_decreases:112` proves strict decrease of the closed-root component when the environment is reset.

The standalone `reset_increases_unseen` kernel gives a concrete failure of using only remaining pairs: before reset, a remembered pair leaves zero unseen pairs; resetting to the empty domain makes that same pair unseen again, increasing the count to one. It is a measure counterexample, not a reachable-state or Haskell defect claim. Reference unfolding also restores a full original Mu record. Raw payload descent is therefore insufficient. The proved local weight assigns references weight one and binders weight zero (`IntersectProgress.LocalWeight:36`), while fresh Mu entry reduces the separate remaining-pair component. Closed-root resets need the extra outer component.

## Validation and scope

Pinned Lean 4.34.1 direct checks passed with all linters enabled: 15 imported axiom/full-signature pairs and three integration axiom/full-signature pairs. All final standalone sources include explicit proof, universe, deep-term and full-name printing with one million print steps. Both commands returned exit 0. Logs contain no warning, error, `sorryAx`, truncation, or omission marker. No production file, Haskell file, Git state, or canonical build was changed.

The conclusions concern the formal source schedule and the literal current checked Lean executor. They do not establish GHC demand order, host mutable-cache publication, FFI/container behavior, solver completeness, all Sized APIs, or general constrained recursive outer convergence. No Haskell defect was found by this audit.
