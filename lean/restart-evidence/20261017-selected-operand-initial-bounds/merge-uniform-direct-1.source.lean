import MicroCFTA.SourceCurrentMemoMergeNumeric

/-!
# Uniform initial resource bounds for general Merge

Complete payload mass bounds ordinary input height. One initial scalar
therefore determines both worker fuels without a projected future input.
The completed call retains its exact result, full heap, and populated memo.
-/
namespace MicroCFTA.SourceCurrentMemoMergeUniformNumeric
open InternedConstructorTemplates InternedProbeProvenance
open MergedOrdinaryHeight
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph (Call Memo)
open SourceCurrentMemoMergeEffects (Effect Stored)
open SourceCurrentMemoMergeResourceControl (Fits)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

mutual
/-- Complete value mass bounds the ordinary height used by the source Merge worker. -/
theorem height_le_mass (input : Value Symbol Guard) : height input ≤ InternedValueMass.value input := by
  cases input with
  | node entry rows level free =>
      have smaller := edgesHeight_le_mass rows
      simp only [height, InternedValueMass.value]
      omega
  | empty | reference | union | mu => simp only [height]; omega
termination_by sizeOf input

/-- Complete edge mass bounds the ordinary height below that edge. -/
theorem edgeHeight_le_mass (row : EdgeValue Symbol Guard) : edgeHeight row ≤ InternedValueMass.edge row := by
  cases row with
  | mk entry children =>
      have smaller := childrenHeight_le_mass children
      simp only [edgeHeight, InternedValueMass.edge]
      omega
termination_by sizeOf row

/-- Complete row-list mass bounds every ordinary row height. -/
theorem edgesHeight_le_mass (rows : List (EdgeValue Symbol Guard)) : edgesHeight rows ≤ InternedValueMass.edges rows := by
  cases rows with
  | nil => rfl
  | cons first rest =>
      have own := edgeHeight_le_mass first
      have later := edgesHeight_le_mass rest
      simp only [edgesHeight, InternedValueMass.edges]
      omega
termination_by sizeOf rows

/-- Complete child-list mass bounds every ordinary child height. -/
theorem childrenHeight_le_mass (children : List (Value Symbol Guard)) :
    childrenHeight children ≤ InternedValueMass.values children := by
  cases children with
  | nil => rfl
  | cons first rest =>
      have own := height_le_mass first
      have later := childrenHeight_le_mass rest
      simp only [childrenHeight, InternedValueMass.values]
      omega
termination_by sizeOf children
end

/-- One current scalar bounds both ordinary request height and all initial heap resources. -/
def workFuel (bound : Nat) : Nat := SourceCurrentMemoMergeNumericControl.bound bound bound

/-- The same work ceiling supplies every actual nested selection. -/
def selectionFuel (bound : Nat) : Nat :=
  SourceMergedComparisonNumeric.comparisonFuel (workFuel bound) (workFuel bound) (workFuel bound)

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed exact call replays at the scalar-only fuels and derives its final resources. -/
theorem of_call {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (bound : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Stored before memo)
    (available : Available before input) (fits : Fits bound before) :
    SourceCurrentMemoMergeWorker.call clear top (workFuel bound) (selectionFuel bound)
      input before memo = .done output after saved ∧
      Fits (workFuel bound) after ∧ InternedValueMass.value output ≤ workFuel bound ∧
      ∀ workExtra selectionExtra,
        SourceCurrentMemoMergeWorker.call clear top (workFuel bound + workExtra)
          (selectionFuel bound + selectionExtra) input before memo = .done output after saved := by
  have bounded := Nat.le_trans (height_le_mass input)
    (InternedValueMassHeap.available before fits.stored input available)
  obtain ⟨cost, measured, trace, paid⟩ := SourceCurrentMemoMergeNumeric.call_bound bound actual bound
    semantic costs physical available fits bounded
  have ready := trace.selection_ready
  have finalFits := trace.final_fits
  refine ⟨SourceCurrentMemoMergeMeasured.call_replay measured _ ready _ _ paid (Nat.le_refl _),
    finalFits, InternedValueMassHeap.available after finalFits.stored output
      (SourceCurrentMemoMergeEffects.call_effects actual semantic costs physical available).2.2.1, ?_⟩
  intro workExtra selectionExtra
  exact SourceCurrentMemoMergeMeasured.call_replay measured _ ready _ _
    (Nat.le_trans paid (Nat.le_add_right _ _)) (Nat.le_add_right _ _)

/-- Initial physical facts construct complete general Merge using only a scalar resource forecast. -/
theorem complete (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (bound : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Stored before memo)
    (available : Available before input) (fits : Fits bound before) :
    ∃ output after saved,
      Call clear top input before memo output after saved ∧
      SourceCurrentMemoMergeWorker.call clear top (workFuel bound) (selectionFuel bound)
        input before memo = .done output after saved ∧
      Effect before after ∧ Stored after saved ∧ Available after output ∧
      (input.free = [] → output.free = []) ∧ Fits (workFuel bound) after ∧
      InternedValueMass.value output ≤ workFuel bound ∧
      ∀ workExtra selectionExtra,
        SourceCurrentMemoMergeWorker.call clear top (workFuel bound + workExtra)
          (selectionFuel bound + selectionExtra) input before memo = .done output after saved := by
  obtain ⟨output, after, saved, actual, effect, retained, result, closed⟩ :=
    SourceCurrentMemoMergeCompletion.call_complete clear top input before memo semantic costs physical available
  have checked := of_call actual bound semantic costs physical available fits
  exact ⟨output, after, saved, actual, checked.1, effect, retained, result, closed,
    checked.2.1, checked.2.2.1, checked.2.2.2⟩

end
end MicroCFTA.SourceCurrentMemoMergeUniformNumeric
