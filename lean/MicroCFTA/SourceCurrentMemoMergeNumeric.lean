import MicroCFTA.SourceCurrentMemoMergeResourceIteration
import MicroCFTA.SourceCurrentMemoMergeWorkWidths
import MicroCFTA.SourceCurrentMemoMergeCompletion

/-!
# Initial numeric budgets for general memo-aware Merge

Ordinary request height bounds recursive calls. Direct instruction counts
compose literal constructor and selection growth at their actual heaps.
The resulting initial scalar bounds every heap and the additive worker
cost. One computed selection fuel replays the complete measured graph.
-/
namespace MicroCFTA.SourceCurrentMemoMergeNumeric
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph (Call Memo body winner remember)
open SourceCurrentMemoMergeEffects (Effect Contract Stored)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentMemoMergeMeasured (MeasuredRun MeasuredCall)
open SourceCurrentMemoMergeResourceTrace (Trace CallTrace)
open SourceCurrentMemoMergeNumericControl (width step bound)
open HeightOrderControlled (iterate)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

private theorem body_zero [DecidableEq Symbol] (top : Guard) (input : Value Symbol Guard)
    (bounded : MergedOrdinaryHeight.height input ≤ 0) : body top input = .pure input := by
  cases input with
  | node => simp only [MergedOrdinaryHeight.height] at bounded; omega
  | empty | reference | mu | union => rfl

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial height and current scalar resources bound the same actual completed call. -/
theorem call_bound (height : Nat) {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Stored before memo)
    (available : Available before input) (fits : Fits resource before)
    (bounded : MergedOrdinaryHeight.height input ≤ height) :
    ∃ cost, ∃ measured : MeasuredCall clear top cost input before memo output after saved,
      CallTrace (bound height resource) measured ∧ cost ≤ bound height resource := by
  induction height generalizing input output before after memo saved resource with
  | zero =>
      cases actual with
      | hit found =>
          exact ⟨1, .hit found, .hit found (fits.mono (by simp only [bound]; omega)), by simp only [bound]; omega⟩
      | @miss memo input before candidate after current absent actual =>
          have direct := actual
          rw [body_zero top input bounded] at direct
          obtain ⟨same, sameHeap, sameMemo⟩ := SourceCurrentMemoMergeGraph.Run.pure_iff.mp direct
          subst candidate after current
          have bodyTrace : ∃ measured : MeasuredRun clear top 1 (body top input) before memo input before memo,
              Trace (bound 0 resource) measured := by
            rw [body_zero top input bounded]
            exact ⟨.pure input before memo, .pure input before memo (fits.mono (by simp only [bound]; omega))⟩
          obtain ⟨measured, trace⟩ := bodyTrace
          exact ⟨2, .miss absent measured, .miss absent trace, by simp only [bound]; omega⟩
  | succ height ih =>
      cases actual with
      | hit found =>
          have enough := SourceCurrentMemoMergeNumericControl.bound_ge (height + 1) resource
          exact ⟨1, .hit found, .hit found (fits.mono (by omega)), by omega⟩
      | @miss memo input before candidate after current absent actual =>
          obtain ⟨events, directCost, counted⟩ := SourceCurrentMemoMergeDirectCost.of_run actual
          have mass := InternedValueMassHeap.available before fits.stored input available
          have directBound := SourceCurrentMemoMergeDirectCost.body_cost input resource mass counted
          have checked := SourceCurrentMemoMergeWorkWidths.body_checked clear top input before semantic costs available resource mass
          have reached := counted.erase.bounded (MergedOrdinaryHeight.height input)
            (fun after output => Contract input before output after) semantic costs physical
            (SourceCurrentMemoMergeRequestBounds.body_bounded clear top input before semantic costs available)
          have requests : SourceCurrentMemoMergeResourceIteration.Requests (bound height) clear top events := by
            intro event member currentBound currentFits
            have localFacts := reached.2.2.2 event member
            exact ih (counted.erase.calls event member) currentBound localFacts.2.1.semantic localFacts.2.1.costs
              localFacts.2.2.1 localFacts.2.2.2 currentFits (by have smaller := localFacts.1; omega)
          obtain ⟨cost, measured, trace, paid⟩ := SourceCurrentMemoMergeResourceIteration.Counted.resources counted
            (bound height) (width resource) resource _ semantic costs physical checked fits requests
          have grows : ∀ value, value ≤ step (width resource) (bound height) value :=
            fun value => Nat.le_trans (Nat.le_succ value) (SourceCurrentMemoMergeNumericControl.step_ge _ _ value)
          have larger := SourceCurrentMemoMergeNumericControl.iterate_count_mono
            (step (width resource) (bound height)) grows directBound resource
          have finalBound : iterate (step (width resource) (bound height)) directCost resource ≤ bound (height + 1) resource := by
            change _ ≤ iterate (step (width resource) (bound height)) (SourceCurrentMemoMergeDirectCost.bodyBudget resource) resource + 1
            omega
          refine ⟨cost + 1, .miss absent measured, .miss absent (trace.mono finalBound), ?_⟩
          change cost + 1 ≤ iterate (step (width resource) (bound height)) (SourceCurrentMemoMergeDirectCost.bodyBudget resource) resource + 1
          omega

end

/-- Initial literal input height, counters, and causal mass determine the work budget. -/
def workFuel (input : Value Symbol Guard) (nodes edges mass : Nat) : Nat :=
  bound (MergedOrdinaryHeight.height input) (SourceCurrentMemoMergeResourceControl.initialBound nodes edges mass)

/-- One scalar ceiling supplies every demanded selection in the complete call. -/
def selectionFuel (input : Value Symbol Guard) (nodes edges mass : Nat) : Nat :=
  let ceiling := workFuel input nodes edges mass
  SourceMergedComparisonNumeric.comparisonFuel ceiling ceiling ceiling

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial facts construct the complete general call at its own computed fuels. -/
theorem complete (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (mass : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Stored before memo)
    (available : Available before input) (stored : InternedValueMassHeap.Stored mass before) :
    ∃ output after saved,
      Call clear top input before memo output after saved ∧
      SourceCurrentMemoMergeWorker.call clear top
        (workFuel input before.nodes.next before.edges.next mass)
        (selectionFuel input before.nodes.next before.edges.next mass) input before memo = .done output after saved ∧
      Effect before after ∧ Stored after saved ∧ Available after output ∧
      (input.free = [] → output.free = []) ∧
      Fits (workFuel input before.nodes.next before.edges.next mass) after ∧
      InternedValueMass.value output ≤ workFuel input before.nodes.next before.edges.next mass ∧
      ∀ workExtra selectionExtra,
        SourceCurrentMemoMergeWorker.call clear top
          (workFuel input before.nodes.next before.edges.next mass + workExtra)
          (selectionFuel input before.nodes.next before.edges.next mass + selectionExtra) input before memo = .done output after saved := by
  obtain ⟨output, after, saved, actual, effect, retained, result, closed⟩ :=
    SourceCurrentMemoMergeCompletion.call_complete clear top input before memo semantic costs physical available
  obtain ⟨cost, measured, trace, paid⟩ := call_bound (MergedOrdinaryHeight.height input) actual _ semantic costs physical available
    (SourceCurrentMemoMergeResourceControl.initial before mass stored) (Nat.le_refl _)
  have ready := trace.selection_ready
  have done := SourceCurrentMemoMergeMeasured.call_replay measured _ ready _ _ paid (Nat.le_refl _)
  have finalFits := trace.final_fits
  refine ⟨output, after, saved, actual, done, effect, retained, result, closed, finalFits,
    InternedValueMassHeap.available after finalFits.stored output result, ?_⟩
  intro workExtra selectionExtra
  exact SourceCurrentMemoMergeMeasured.call_replay measured _ ready _ _
    (Nat.le_trans paid (Nat.le_add_right _ _)) (Nat.le_add_right _ _)

end

end MicroCFTA.SourceCurrentMemoMergeNumeric
