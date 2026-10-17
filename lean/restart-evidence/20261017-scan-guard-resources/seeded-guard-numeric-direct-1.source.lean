import MicroCFTA.SourceCurrentConstrainedCapSeededNumeric
import MicroCFTA.SourceCurrentSeededGuardForecast
import MicroCFTA.SourceCurrentSeededProjectionCarrier

/-!
# Initial first-seeded queries with a finite guard forecast

The producer constructs each projection, recursive tail, and native query.
The same exact returns retain the existing numeric and language receipts.
The alphabet follows the initial profile schedule. Selected support permits
unrelated open siblings. No future ranges or finite input cap is required.
-/
namespace MicroCFTA.SourceCurrentSeededGuardNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapSeededForecast
open SourceCurrentSeededGuardForecast (foldAlphabet finalAlphabet)
open SourceCurrentConstrainedCapSeededNumeric (Receipt)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded)
open SourceCurrentAllocatedSeededMemos (OperandReads FoldReads SeededReads)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededLanguage (Includes)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem cons_reads {values : List (Value Symbol Guard)} {seed path : List Int} {paths : List (List Int)}
    {before middle later after : Checked width} {head tail result : Value Symbol Guard} {nativeFuel : Nat}
    {first : Operand path values before head middle} {rest : Fold values (paths ++ [seed]) middle tail later}
    {native : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later
      (.code (.pure result)) after} {memos middleMemos laterMemos : Memos}
    (firstReads : OperandReads first memos middleMemos) (restReads : FoldReads rest middleMemos laterMemos)
    (nativeReads : SourceCurrentAllocatedSeededMemos.NativeReads native laterMemos laterMemos) :
    ∃ actual : Fold values ((path :: paths) ++ [seed]) before result after, FoldReads actual memos laterMemos := by
  cases paths <;> exact ⟨.cons first rest native, .cons firstReads restReads nativeReads⟩

/-- Initial selected support constructs the literal right fold at one computed ceiling. -/
theorem fold_complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked (bits + 2)) (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ seed :: paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ seed :: paths, path ≠ [])
    (reserved : Reserved bits values.length seed paths profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after next final, ∃ actual : Fold values (paths ++ [seed]) before result after,
      FoldReads actual memos final ∧ Receipt formulas solver next before result after memos final ∧
      Fits (foldProfile values.length seed paths profile) after ∧ Includes formulas solver values (seed :: paths) result ∧
      SourceCurrentAllocatedSeededWorker.fold
        (foldFuel values.length seed paths profile) (foldFuel values.length seed paths profile)
        (foldFuel values.length seed paths profile) values seed paths before = .done result after ∧
      Heap (fun guard => guard ∈ foldAlphabet alphabet values.length seed paths profile) after.native.machine.heap := by
  induction paths generalizing alphabet inventory before profile memos with
  | nil =>
      obtain ⟨result, after, final, actual, reads, finalFrame, finalFits, effects, extension, resident, closed, globals, done⟩ :=
        SourceCurrentConstrainedCapSeededProjection.complete formulas solver inventory unconstrained anchor anchorSemantic anchorReady
          seed values before profile frame fits available growth (supported seed List.mem_cons_self) memos valid
      have carrier := SourceCurrentSeededProjectionCarrier.operand (fun guard => guard ∈ alphabet)
        unconstrained anchor anchorSemantic anchorReady actual frame.ready.semantic available growth
        (supported seed List.mem_cons_self) known
      refine ⟨result, after, inventory, final, .one actual, .one reads,
        ⟨finalFrame, effects, extension, resident, closed, globals,
          fun probes => SourceCurrentAllocatedProbeQuery.operand_heap actual frame.ready available probes⟩,
        finalFits, ?_, done, carrier⟩
      intro ambient symbol terms part accepted selected
      exact SourceCurrentAllocatedSeededOperandLanguage.Operand.included unconstrained anchor anchorSemantic anchorReady
        actual (SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs)
        available growth (supported seed List.mem_cons_self) (proper seed List.mem_cons_self)
        (SourceEqualityPCSGuard.holds formulas solver) ambient symbol terms part accepted (selected seed List.mem_cons_self)
  | cons path paths ih =>
      obtain ⟨head, middle, middleMemos, first, firstReads, middleFrame, middleFits, firstEffects,
        firstExtension, headAvailable, headClosed, firstGlobals, firstDone⟩ :=
        SourceCurrentConstrainedCapSeededProjection.complete formulas solver inventory unconstrained anchor anchorSemantic anchorReady
          path values before profile frame fits available growth (supported path (by simp)) memos valid
      have middleKnown := SourceCurrentSeededProjectionCarrier.operand (fun guard => guard ∈ alphabet)
        unconstrained anchor anchorSemantic anchorReady first frame.ready.semantic available growth
        (supported path (by simp)) known
      obtain ⟨tail, later, next, laterMemos, rest, restReads, restReceipt, laterFits, restIncluded, restDone, restKnown⟩ :=
        ih alphabet inventory middle (projectionProfile path values.length profile) middleFrame middleFits
          (fun value member => firstEffects.keeps.available value (available value member))
          (grows_trans growth firstEffects.keeps.growth)
          (fun value member => supported value (by simp only [List.mem_cons] at member ⊢; exact member.elim Or.inl (fun found => Or.inr (Or.inr found))))
          (fun value member => proper value (by simp only [List.mem_cons] at member ⊢; exact member.elim Or.inl (fun found => Or.inr (Or.inr found))))
          reserved.1 middleKnown middleMemos firstGlobals.valid
      obtain ⟨last, nativeFuel, result, after, native, carrier⟩ := SourceCurrentGeneratedQueryGuardResources.complete
        (foldAlphabet alphabet values.length seed paths (projectionProfile path values.length profile))
        (foldProfile values.length seed paths (projectionProfile path values.length profile)) formulas solver next later
        restReceipt.frame laterFits reserved.2 head tail (restReceipt.effects.keeps.available head headAvailable)
        restReceipt.available headClosed restReceipt.closed restKnown laterMemos restReceipt.globals.valid
      have headAt := SourceCurrentAllocatedSeededWorkerStability.operand_done_stable firstDone
        (fuel_head values.length seed path paths profile) (fuel_head values.length seed path paths profile)
      have tailAt := SourceCurrentAllocatedSeededWorkerStability.fold_done_stable restDone
        (fuel_tail values.length seed path paths profile) (fuel_tail values.length seed path paths profile)
        (fuel_tail values.length seed path paths profile)
      have nativeAt := SourceEqualityNativeDemand.done_stable (queryFuel (foldProfile values.length seed paths (projectionProfile path values.length profile)))
        (foldFuel values.length seed (path :: paths) profile - queryFuel (foldProfile values.length seed paths (projectionProfile path values.length profile))) _ later after result native.done
      rw [Nat.add_sub_of_le (fuel_query values.length seed path paths profile)] at nativeAt
      obtain ⟨events, runs, silent⟩ := native.query.events
      obtain ⟨actual, reads⟩ := cons_reads (native := native.trace) firstReads restReads (.silent events runs silent)
      refine ⟨result, after, last, laterMemos, actual, reads,
        ⟨native.frame, firstEffects.trans (restReceipt.effects.trans native.query.effects),
          firstExtension.trans (restReceipt.extension.trans native.query.extension), native.query.available, native.query.closed,
          ⟨firstEffects.keeps.trans (restReceipt.effects.keeps.trans native.query.effects.keeps),
            native.frame.ready.semantic, native.frame.ready.costs, native.query.globals,
            extends_trans firstGlobals.retained restReceipt.globals.retained,
            restReceipt.globals.query.trans firstGlobals.query⟩,
          fun probes => SourceCurrentAllocatedMuRebuild.trace_heap native.trace restReceipt.frame.ready.semantic
            (restReceipt.probes (SourceCurrentAllocatedProbeQuery.operand_heap first frame.ready available probes))⟩,
        native.fits, ?_, ?_, carrier⟩
      · intro ambient symbol terms part accepted selected
        have own := SourceCurrentAllocatedSeededOperandLanguage.Operand.included unconstrained anchor anchorSemantic anchorReady
          first (SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs)
          available growth (supported path (by simp)) (proper path (by simp))
          (SourceEqualityPCSGuard.holds formulas solver) ambient symbol terms part accepted (selected path (by simp))
        have tail := restIncluded ambient symbol terms part accepted
          (fun value member => selected value (by simp only [List.mem_cons] at member ⊢; exact member.elim Or.inl (fun found => Or.inr (Or.inr found))))
        exact (native.query.meaning ambient part).mpr ⟨own, tail⟩
      · simp only [SourceCurrentAllocatedSeededWorker.fold, headAt, tailAt,
          SourceCurrentAllocatedSeededWorker.Outcome.bind, SourceCurrentAllocatedSeededWorker.leaf, nativeAt]

/-- The original first path stays the final seed, with no reached-range premise. -/
theorem complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (reserved : SeededReserved bits values.length paths profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after next final, ∃ actual : Seeded values paths before result after,
      SeededReads actual memos final ∧ Receipt formulas solver next before result after memos final ∧
      Fits (finalProfile values.length paths profile) after ∧
      (paths ≠ [] → Includes formulas solver values paths result) ∧
      SourceCurrentAllocatedSeededWorker.seeded
        (fuel values.length paths profile) (fuel values.length paths profile) (fuel values.length paths profile)
        values paths before = .done result after ∧
      Heap (fun guard => guard ∈ finalAlphabet alphabet values.length paths profile) after.native.machine.heap := by
  cases paths with
  | nil =>
      exact ⟨.empty, before, inventory, memos, .nil before, .nil,
        ⟨frame, .refl _ (SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs),
          .refl _, empty_available _, rfl,
          ⟨pure_keeps _ frame.ready.semantic.ready, frame.ready.semantic, frame.ready.costs, valid, extends_refl _, rfl⟩, fun probes => probes⟩,
        fits, fun nonempty => False.elim (nonempty rfl), rfl, known⟩
  | cons seed rest =>
      obtain ⟨result, after, next, final, actual, reads, receipt, finalFits, included, done, carrier⟩ := fold_complete
        alphabet formulas solver inventory unconstrained anchor anchorSemantic anchorReady values seed rest before profile
        frame fits available growth supported proper reserved known memos valid
      exact ⟨result, after, next, final, .nonempty actual, .nonempty reads, receipt, finalFits, fun _ => included, done, carrier⟩

end MicroCFTA.SourceCurrentSeededGuardNumeric
