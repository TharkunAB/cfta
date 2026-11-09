import MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
import MicroCFTA.SourceCurrentAllocatedTargetCallerGuardResources
import MicroCFTA.SourceCurrentAllocatedTargetCallerCreditResources
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerResources
import MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations

/-!
# Current resources for the same incoming shared query

Current admission derives native word ranges before the intersection.
The resulting guard inventory supplies the shared worker forecast and
both observation ceilings. The original successful packet retains its
actual observed outcome and ordered global memo bundle. A second resource
proof contributes only bounds and replay for that same checked success.

The admission condition is explicit. This proof does not establish native
capacity for every original input or select the complete recursive driver.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile step)
open SourceCurrentAllocatedNativeCreditProfile (Admits)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "currentTupleBudget" => SourceCurrentConjunctionTupleBudget.currentTupleBudget
local notation "workerFuel" => SourceCurrentAllocatedSharedConjunctionWorkerActual.projectionFuel
local notation "readerFuel" => SourceCurrentAllocatedSharedConjunctionWorkerActual.readerFuel
variable {bits : Nat}

/-- The native query forecast supplies the fixed alphabet and entry profile for the shared worker. -/
noncomputable def forecast (alphabet : List Constraint) (profile : Profile) : Profile :=
  SourceCurrentAllocatedSharedConjunctionWorkerActual.forecast_with_alphabet
    (queryAlphabet alphabet profile) currentTupleBudget (step profile)

private theorem shared_ge (alphabet : List Constraint) (budget : Nat) (profile : Profile) :
    SourceCurrentAllocatedNativeResourceForecast.Le profile
      (SourceCurrentAllocatedSharedConjunctionWorkerActual.forecast_with_alphabet alphabet budget profile) := by
  have scalarBound : SourceCurrentConstrainedCapTargetForecast.scalar profile ≤
      SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast alphabet budget
        (SourceCurrentConstrainedCapTargetForecast.scalar profile) :=
    Nat.le_trans (Nat.le_max_left _ _)
      (SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast_ge _ _ _)
  change profile.nodes ≤ _ ∧ profile.edges ≤ _ ∧ profile.domains ≤ _ ∧ profile.mass ≤ _
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes _) scalarBound,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges _) scalarBound, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass _) scalarBound⟩

/-- The combined native and shared forecast retains each initial resource component. -/
theorem forecast_ge (alphabet : List Constraint) (profile : Profile) :
    SourceCurrentAllocatedNativeResourceForecast.Le profile (forecast alphabet profile) :=
  (SourceCurrentAllocatedNativeResourceForecast.step_ge profile).trans
    (shared_ge (queryAlphabet alphabet profile) currentTupleBudget (step profile))

/-- Current admission and guard bounds complete the same incoming packet at explicit ceilings. -/
theorem complete_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (left right : Node) (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (leftAvailable : Available beforeCaller.checked.native.machine.heap left)
    (rightAvailable : Available beforeCaller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Admits bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    ∃ (next : Inventory) (query : Node) (queried : Checked (bits + 2))
      (answer : Bool) (checkedAfter : Checked (bits + 2)) (saved : Fourth)
      (final : Memos) (queries : Queries) (replacement : Node) (handle fuel p h : Nat)
      (observed : Observed (bits + 2)),
      next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        beforeCaller.checked query queried memos ∧
      (∀ extra, SourceEqualityNativeDemand.execute (fuel + extra)
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked = .done query queried) ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then
          SourcePruningEnumerationSharedEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
        else (.skipped queried beforeCaller.fourth, memos.query)) =
          (observed, queries)) ∧
      observed.completed = some answer ∧ observed.state = checkedAfter ∧ observed.memo = saved ∧
      Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
      final.query = queries ∧ Cache.Extends memos.unfolding final.unfolding ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      replacement = (if answer then .empty else query) ∧
      Available checkedAfter.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode checkedAfter.native.machine.heap handle = some replacement ∧
      (∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) ∧
      (checkEmpty = false → answer = false ∧ replacement = query ∧ checkedAfter = queried ∧
        saved = beforeCaller.fourth ∧ queries = memos.query ∧ final = memos) ∧
      (checkEmpty = true → ∃ reached,
        SourceEndpointMemo.run query memos.query = (reached, queries) ∧
        SourceEndpointMemoCorrect.Checked queried.native.machine.heap memos.query
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained query) (reached, queries) ∧
        (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
          final = {memos with query := queries}) ∧
        (reached = true → ∃ (baseP baseH : Nat) (snapshot : Snapshot),
          SourceCurrentAllocatedSharedConjunctionWorker.call baseP baseH
              SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried beforeCaller.fourth =
            .done answer checkedAfter saved snapshot ∧
          SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads baseP baseH
            SourceCurrentConjunctionTupleBudget.currentTupleBudget beforeCaller.fourth query
            (physical queried) {memos with query := queries} final)) ∧
      Fits (step profile) queried ∧ Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) checkedAfter.native.machine.heap ∧
      fuel = instructionBound profile.nodes profile.edges profile.mass + 1 ∧
      p = workerFuel (queryAlphabet alphabet profile) currentTupleBudget (step profile) ∧
      h = readerFuel (queryAlphabet alphabet profile) currentTupleBudget (step profile) := by
  have ranges := SourceCurrentAllocatedTargetQuery.ready_admitted_ranges profile beforeCaller.checked
    initial.ready fits room left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
      oldFuel, oldP, oldH, observed, source, roots, receipt, native, phase, completed, observedState,
      observedMemo, post, querySame, unfolding, sound, replacementEq, available, closed, encoded,
      decoded, meaning, disabled, enabled⟩ :=
    complete formulas solver inventory beforeCaller left right checkEmpty memos initial
      leftAvailable rightAvailable leftClosed rightClosed ranges
  have nativeDone : SourceEqualityNativeDemand.execute oldFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done query queried := by
    simpa only [Nat.add_zero] using native 0
  obtain ⟨_next, _source, _roots, _receipt, _post, queryFits, _mass⟩ :=
    SourceCurrentAllocatedTargetQuery.raw_done_caller_admitted_resources profile oldFuel formulas solver inventory
      beforeCaller queried left right query memos initial fits room leftAvailable rightAvailable
      leftClosed rightClosed nativeDone
  have queryCarrier := receipt.actual.guard_forecast alphabet profile initial.ready fits
    leftAvailable rightAvailable leftClosed rightClosed known
  have computed := receipt.actual.done_profile profile initial.ready fits
    leftAvailable rightAvailable leftClosed rightClosed
  let alphabetAfter := queryAlphabet alphabet profile
  let p := workerFuel alphabetAfter currentTupleBudget (step profile)
  let h := readerFuel alphabetAfter currentTupleBudget (step profile)
  have checkedGe : SourceCurrentAllocatedNativeResourceForecast.Le (step profile) (forecast alphabet profile) :=
    shared_ge alphabetAfter currentTupleBudget (step profile)
  have finalData : Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ alphabetAfter) checkedAfter.native.machine.heap ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then
          SourcePruningEnumerationSharedEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
        else (.skipped queried beforeCaller.fourth, memos.query)) = (observed, queries)) := by
    cases checkEmpty with
    | false =>
        obtain ⟨_answer, _replacement, checkedEq, _saved, _queries, _final⟩ := disabled rfl
        refine ⟨checkedEq.symm ▸ queryFits.mono checkedGe, checkedEq.symm ▸ queryCarrier, ?_⟩
        intro P H _enoughP _enoughH
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          phase oldP oldH (Nat.le_refl _) (Nat.le_refl _)
    | true =>
        obtain ⟨reached, guardRun, guardChecked, skipped, performed⟩ := enabled rfl
        cases reached with
        | false =>
            obtain ⟨_answer, checkedEq, _saved, _final⟩ := skipped rfl
            refine ⟨checkedEq.symm ▸ queryFits.mono checkedGe, checkedEq.symm ▸ queryCarrier, ?_⟩
            intro P H _enoughP _enoughH
            simpa only [↓reduceIte, SourcePruningEnumerationSharedEnabledEmpty.check,
              guardRun, Bool.false_eq_true] using
                phase oldP oldH (Nat.le_refl _) (Nat.le_refl _)
        | true =>
            obtain ⟨baseP, baseH, snapshot, actual, _originalReads⟩ := performed rfl
            have queryProbes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap := by
              cases receipt.actual with
              | @run traceFuel trace =>
                  exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
            have queryContext : Context formulas solver next
                (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
                {memos with query := queries} := by
              exact ⟨receipt.ready, receipt.admitted,
                initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
                initial.stored.grows receipt.effects.keeps, initial.covered,
                SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
                ⟨receipt.globals.unfolding, guardChecked.valid⟩, queryProbes⟩
            obtain ⟨_resourceFinal, _advanced, _resourceReads, _resourcePost, _resourceSound, _resident,
                _extends, _same, bounded, replay⟩ :=
              SourceCurrentAllocatedSharedConjunctionWorkerActual.raw_done_resources_with_alphabet
                formulas solver alphabetAfter (step profile) queryContext queryFits receipt.available queryCarrier actual
            simp only [SourceCurrentAllocatedPartialState.advance] at replay
            obtain ⟨raw, advanced⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done actual
            have ready := SourceCurrentAllocatedConjunctionMemo.ready queried receipt.ready.good
              receipt.ready.semantic receipt.ready.costs
            have retained := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap
              (fun guard => guard ∈ alphabetAfter) baseP baseH currentTupleBudget beforeCaller.fourth
              query (physical queried) ready queryCarrier receipt.available
            rw [raw] at retained
            have carrier : Heap (fun guard => guard ∈ alphabetAfter) checkedAfter.native.machine.heap := by
              rw [advanced]
              change Heap (fun guard => guard ∈ alphabetAfter)
                (physical (advancePhysical queried snapshot.storage.requirements.physical)).heap
              rw [SourceCurrentAllocatedQueryMemo.physical_advance]
              simpa only [SourceCurrentConjunctionSharedWorker.Outcome.state] using retained
            have observedEq : observed = .performed (.done answer checkedAfter saved snapshot) := by
              have original := phase (max oldP p) (max oldH h)
                (Nat.le_max_left _ _) (Nat.le_max_left _ _)
              have stable := replay (max oldP p) (max oldH h)
                (Nat.le_max_right _ _) (Nat.le_max_right _ _)
              have same : ((.performed (.done answer checkedAfter saved snapshot) : Observed (bits + 2)), queries) =
                  (observed, queries) := by
                simpa only [↓reduceIte, SourcePruningEnumerationSharedEnabledEmpty.check, guardRun, stable] using original
              exact (congrArg Prod.fst same).symm
            refine ⟨bounded, carrier, ?_⟩
            intro P H enoughP enoughH
            rw [observedEq]
            simp only [↓reduceIte, SourcePruningEnumerationSharedEnabledEmpty.check, guardRun,
              replay P H enoughP enoughH]
  refine ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
    instructionBound profile.nodes profile.edges profile.mass + 1, p, h, observed, source, roots, receipt,
    ?_, finalData.2.2, completed, observedState, observedMemo, post, querySame, unfolding, sound,
    replacementEq, available, closed, encoded, decoded, meaning, disabled, enabled,
    queryFits, finalData.1, finalData.2.1, rfl, rfl, rfl⟩
  intro extra
  exact SourceEqualityNativeDemand.done_stable _ extra _ beforeCaller.checked queried query computed

end MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
