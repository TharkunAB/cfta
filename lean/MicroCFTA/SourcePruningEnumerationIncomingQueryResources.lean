import MicroCFTA.SourcePruningEnumerationIncomingQuery
import MicroCFTA.SourceCurrentAllocatedTargetCallerGuardResources
import MicroCFTA.SourceCurrentConjunctionAlphabetBounds

/-!
# Initial resources for the actual incoming intersection and Empty check

The original profile and guard alphabet bound the native intersection and
its enabled emptiness phase. The same returned replacement retains every
existing query, memo and language receipt. No future numeric room is given.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room step)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reaches" => SourceEndpointReachability.reaches SourceMemoGate.unconstrained
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "workerFuel" => SourceCurrentConjunctionWorklistResources.workerFuel
local notation "readerFuel" => SourceCurrentConjunctionWorklistResources.readerFuel
variable {bits : Nat}

/-- Initial guard and numeric bounds reserve the query and its optional constructor allocations. -/
noncomputable def forecast (alphabet : List Constraint) (profile : Profile) : Profile :=
  SourceCurrentConjunctionAlphabetBounds.callerForecast (queryAlphabet alphabet profile) 1000 (step profile)

/-- The combined forecast retains every original numeric component. -/
theorem forecast_ge (alphabet : List Constraint) (profile : Profile) :
    SourceCurrentAllocatedNativeResourceForecast.Le profile (forecast alphabet profile) :=
  (SourceCurrentAllocatedNativeResourceForecast.step_ge profile).trans
    (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge _ _ _)

private theorem checked_fits (alphabet : List Constraint) (budget : Nat) (profile : Profile)
    {before : Checked (bits + 2)}
    {after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    (initial : Fits profile before)
    (bounded : SourceCurrentMemoMergeResourceControl.Fits
      (SourceCurrentConjunctionWorklistResources.forecast alphabet budget (scalar profile)) after.heap) :
    Fits (SourceCurrentConjunctionAlphabetBounds.callerForecast alphabet budget profile) (advancePhysical before after) :=
  ⟨bounded.nodes, bounded.edges, initial.domains, bounded.stored⟩

/-- Original current facts construct the complete incoming packet and its final resources. -/
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
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    ∃ (next : Inventory) (query : Node) (queried : Checked (bits + 2))
      (answer : Bool) (checkedAfter : Checked (bits + 2)) (saved : Fourth)
      (final : Memos) (queries : Queries) (replacement : Node) (handle fuel p h : Nat),
      next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        beforeCaller.checked query queried memos ∧
      (∀ extra, SourceEqualityNativeDemand.execute (fuel + extra)
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked = .done query queried) ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then
          SourcePruningEnumerationEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
        else (.done false queried beforeCaller.fourth, memos.query)) =
          (.done answer checkedAfter saved, queries)) ∧
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
        (reached = true →
          ∃ reachedPhysical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula,
            checkedAfter = advancePhysical queried reachedPhysical ∧
            ∃ actual : SourceCurrentConjunctionMemo.Call 1000 beforeCaller.fourth query
                (physical queried) answer reachedPhysical saved,
              SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := queries} final)) ∧
      Fits (step profile) queried ∧ Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) checkedAfter.native.machine.heap ∧
      fuel = instructionBound profile.nodes profile.edges profile.mass + 1 ∧
      p = workerFuel (queryAlphabet alphabet profile) 1000 (scalar (step profile)) ∧
      h = readerFuel (queryAlphabet alphabet profile) 1000 (scalar (step profile)) := by
  have actualRoom := fits.room room
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left
    beforeCaller.checked.native.machine.heap initial.ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right
    beforeCaller.checked.native.machine.heap initial.ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits beforeCaller.checked
    initial.ready.good initial.ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    actualRoom.1 actualRoom.2.1 actualRoom.2.2
  obtain ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
    oldFuel, _oldP, _oldH, source, roots, receipt, native, _phase, post, querySame, unfolding,
    sound, replacementEq, available, closed, encoded, decoded, meaning, disabled, enabled⟩ :=
    complete formulas solver inventory beforeCaller left right checkEmpty memos initial
      leftAvailable rightAvailable leftClosed rightClosed ranges.1
  have done : SourceEqualityNativeDemand.execute oldFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done query queried := by
    simpa only [Nat.add_zero] using native 0
  obtain ⟨_next, _source, _roots, _receipt, _post, queryFits, _mass⟩ :=
    SourceCurrentAllocatedTargetQuery.raw_done_caller_resources profile oldFuel formulas solver inventory
      beforeCaller queried left right query memos initial fits room leftAvailable rightAvailable leftClosed rightClosed done
  have queryCarrier := receipt.actual.guard_forecast alphabet profile initial.ready fits
    leftAvailable rightAvailable leftClosed rightClosed known
  have computed := receipt.actual.done_profile profile initial.ready fits
    leftAvailable rightAvailable leftClosed rightClosed
  let alphabetAfter := queryAlphabet alphabet profile
  let p := workerFuel alphabetAfter 1000 (scalar (step profile))
  let h := readerFuel alphabetAfter 1000 (scalar (step profile))
  have finalData : Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ alphabetAfter) checkedAfter.native.machine.heap ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then SourcePruningEnumerationEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
          else (.done false queried beforeCaller.fourth, memos.query)) = (.done answer checkedAfter saved, queries)) := by
    cases checkEmpty with
    | false =>
        obtain ⟨rfl, _same, rfl, rfl, rfl, _final⟩ := disabled rfl
        refine ⟨queryFits.mono (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge _ _ _), queryCarrier, ?_⟩
        intro P H _enoughP _enoughH
        simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
        obtain ⟨reached, guardRun, _guardChecked, skipped, performed⟩ := enabled rfl
        cases reached with
        | false =>
            obtain ⟨rfl, rfl, rfl, _final⟩ := skipped rfl
            refine ⟨queryFits.mono (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge _ _ _), queryCarrier, ?_⟩
            intro P H _enoughP _enoughH
            simp only [↓reduceIte, SourcePruningEnumerationEnabledEmpty.check,
              guardRun, Bool.false_eq_true]
        | true =>
            obtain ⟨reachedPhysical, same, actual, _reads⟩ := performed rfl
            have ready := SourceCurrentAllocatedConjunctionMemo.ready queried receipt.ready.good
              receipt.ready.semantic receipt.ready.costs
            have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked queryFits).scalar_fits
            have numeric := SourceCurrentConjunctionAlphabetBounds.call_bound alphabetAfter actual
              (scalar (step profile)) ready receipt.available scalarFits queryCarrier
            have carrier := SourceCurrentConjunctionAlphabetBounds.call_carrier alphabetAfter actual
              ready receipt.available queryCarrier
            have bounded : Fits (forecast alphabet profile) (advancePhysical queried reachedPhysical) :=
              checked_fits alphabetAfter 1000 (step profile) queryFits numeric.1
            refine ⟨?_, ?_, ?_⟩
            · simpa only [same] using bounded
            · simpa only [same, SourceCurrentAllocatedQueryMemo.advancePhysical,
                SourceRecursiveIntersectionThunks.advance] using carrier
            · intro P H enoughP enoughH
              simp only [↓reduceIte, SourcePruningEnumerationEnabledEmpty.check, guardRun]
              apply Prod.ext
              · simpa only [same] using
                  (SourceCurrentAllocatedConjunctionWorker.call_lift (numeric.2 P H enoughP enoughH))
              · rfl
  refine ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
    instructionBound profile.nodes profile.edges profile.mass + 1, p, h, source, roots, receipt,
    ?_, finalData.2.2, post, querySame, unfolding, sound, replacementEq, available, closed,
    encoded, decoded, meaning, disabled, enabled, queryFits, finalData.1, finalData.2.1, rfl, rfl, rfl⟩
  intro extra
  exact SourceEqualityNativeDemand.done_stable _ extra _ beforeCaller.checked queried query computed

end MicroCFTA.SourcePruningEnumerationIncomingQuery
