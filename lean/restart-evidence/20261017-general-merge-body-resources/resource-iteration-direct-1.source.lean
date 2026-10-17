import MicroCFTA.SourceCurrentMemoMergeResourceCertificate
import MicroCFTA.SourceCurrentMemoMergeResourceTrace
import MicroCFTA.SourceCurrentMemoMergeNumericControl

/-!
# Resource iteration through exact direct Merge instructions

The direct count pays each constructor, selection, and sequencing step.
Recursive calls use a separate numeric bound at their exact reached heap.
This local composition retains every measured graph and full intermediate
heap. The height induction must discharge the recursive-call bounds.
-/
namespace MicroCFTA.SourceCurrentMemoMergeResourceIteration
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph (Code Memo)
open SourceCurrentMemoMergeEffects (Effect Contract Stored)
open SourceCurrentMemoMergeDirectCost (Counted)
open SourceCurrentMemoMergeResourceCertificate (Checked)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentMemoMergeMeasured (MeasuredRun MeasuredCall)
open SourceCurrentMemoMergeResourceTrace (Trace CallTrace)
open SourceCurrentMemoMergeNumericControl (step)
open HeightOrderControlled (iterate)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Each actual direct request uses its own reached heap and result table. -/
def Requests (child : Nat → Nat) (clear : Guard → Bool) (top : Guard)
    (events : List (SourceCurrentMemoMergeRequestBounds.Occurrence Symbol Guard)) : Prop :=
  ∀ event ∈ events, ∀ bound, Fits bound event.before →
    ∃ cost, ∃ actual : MeasuredCall clear top cost event.input event.before event.memo event.output event.after event.saved,
      CallTrace (child bound) actual ∧ cost ≤ child bound

/-- Direct instruction count composes current resources and all nested measured costs. -/
theorem Counted.resources {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (SourceCurrentMemoMergeRequestBounds.Occurrence Symbol Guard)} {directCost : Nat}
    (actual : Counted clear top code before memo output after saved events directCost) :
    ∀ (child : Nat → Nat) (width bound : Nat) (post : State Symbol Guard → Output → Prop),
      SemanticReady before → CostHeap before → Stored before memo → Checked width clear code before post →
      Fits bound before → Requests child clear top events →
      ∃ cost, ∃ measured : MeasuredRun clear top cost code before memo output after saved,
        Trace (iterate (step width child) directCost bound) measured ∧
          bound + cost ≤ iterate (step width child) directCost bound := by
  induction actual with
  | pure value heap memo =>
      intro child width bound post semantic costs stored checked fits requests
      have enough := SourceCurrentMemoMergeNumericControl.step_ge width child bound
      refine ⟨1, .pure value heap memo, .pure value heap memo (fits.mono ?_), ?_⟩
      · change bound ≤ step width child bound
        omega
      · change bound + 1 ≤ step width child bound
        exact enough
  | work job heap memo =>
      intro child width bound post semantic costs stored checked fits requests
      have enough := SourceCurrentMemoMergeNumericControl.step_ge width child bound
      have returned := (checked.2.1 bound fits).mono
        (SourceCurrentMemoMergeNumericControl.step_primitive width child bound)
      refine ⟨1, .work job heap memo, .work job heap memo (fits.mono ?_) returned, ?_⟩
      · change bound ≤ step width child bound
        omega
      · change bound + 1 ≤ step width child bound
        exact enough
  | @select inputs heap values after memo fuel done =>
      intro child width bound post semantic costs stored checked fits requests
      have checkedSelection := SourceCurrentMemoMergeResourceControl.selection_replay clear fuel inputs heap bound
        semantic fits checked.1 checked.2.1 values after done
      have returned := checkedSelection.2.1.mono
        (SourceCurrentMemoMergeNumericControl.step_selection width child bound)
      have enough := SourceCurrentMemoMergeNumericControl.step_ge width child bound
      refine ⟨1, .select fuel done, .select fuel done semantic (fits.mono ?_) checked.1 checked.2.1 returned, ?_⟩
      · change bound ≤ step width child bound
        omega
      · change bound + 1 ≤ step width child bound
        exact enough
  | @request input before memo output after saved actual =>
      intro child width bound post semantic costs stored checked fits requests
      obtain ⟨cost, measured, trace, paid⟩ := requests _ (by simp) bound fits
      have enough := SourceCurrentMemoMergeNumericControl.step_pays_child width child bound
      refine ⟨cost + 1, .request measured, .request (trace.mono ?_), ?_⟩
      · exact SourceCurrentMemoMergeNumericControl.step_child width child bound
      · change bound + (cost + 1) ≤ step width child bound
        omega
  | @bind First firstCode before memo value middle current earlier firstCost Output next output after saved
      following laterCost first later firstIH laterIH =>
      intro child width bound post semantic costs stored checked fits requests
      obtain ⟨intermediate, firstChecked, laterChecked⟩ := checked
      have firstPhysical := SourceCurrentMemoMergeEffects.run_effects first.graph intermediate semantic costs stored firstChecked.erase
      obtain ⟨firstMeasuredCost, firstMeasured, firstTrace, firstPaid⟩ :=
        firstIH child width bound intermediate semantic costs stored firstChecked fits
          (fun event member => requests event (List.mem_append_left _ member))
      obtain ⟨laterMeasuredCost, laterMeasured, laterTrace, laterPaid⟩ :=
        laterIH child width (iterate (step width child) firstCost bound) post firstPhysical.1.semantic firstPhysical.1.costs
          firstPhysical.2.1 (laterChecked _ _ firstPhysical.1 firstPhysical.2.2) firstTrace.final_fits
          (fun event member => requests event (List.mem_append_right _ member))
      have grows : ∀ value, value ≤ step width child value :=
        fun value => Nat.le_trans (Nat.le_succ value) (SourceCurrentMemoMergeNumericControl.step_ge width child value)
      have middleBound := SourceCurrentMemoMergeNumericControl.iterate_ge (step width child) grows laterCost
        (iterate (step width child) firstCost bound)
      have finalStep := SourceCurrentMemoMergeNumericControl.step_ge width child
        (iterate (step width child) laterCost (iterate (step width child) firstCost bound))
      have same : iterate (step width child) (firstCost + laterCost + 1) bound =
          step width child (iterate (step width child) laterCost (iterate (step width child) firstCost bound)) := by
        rw [SourceCurrentMemoMergeNumericControl.iterate_succ_right, SourceCurrentMemoMergeNumericControl.iterate_add]
      refine ⟨firstMeasuredCost + laterMeasuredCost + 1, .bind firstMeasured laterMeasured, ?_, ?_⟩
      · apply Trace.bind
        · exact firstTrace.mono (by rw [same]; omega)
        · exact laterTrace.mono (by rw [same]; omega)
      · rw [same]
        omega

end MicroCFTA.SourceCurrentMemoMergeResourceIteration
