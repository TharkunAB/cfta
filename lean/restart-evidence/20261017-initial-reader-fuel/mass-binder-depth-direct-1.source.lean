import MicroCFTA.InternedValueMassHeap
import MicroCFTA.InternedMuDepthInventory

/-!
# Initial Mu degrees from causal payload mass

Stored-plan binder depth is below the complete payload mass. The same
causal store bound therefore bounds every initial Mu degree. Cached depth,
symbols, guards, and free-name magnitudes need no numeric bound.
-/
namespace MicroCFTA.InternedValueMassBinderDepth
open InternedConstructorTemplates
open InternedStoredPlanBinderDepth
variable {Symbol Guard : Type}

mutual
/-- Full payload mass bounds the open binders in the actual stored plan. -/
theorem value_lt (value : Value Symbol Guard) : valueDepth value < InternedValueMass.value value := by
  rw [valueDepth.eq_def]
  split
  · exact InternedValueMass.value_pos value
  · cases value with
    | empty | reference => simp only [InternedValueMass.value]; omega
    | node entry rows depth free =>
        have smaller := edges_le rows
        simp only [InternedValueMass.value]
        omega
    | union entry members depth free =>
        have smaller := many_le members
        simp only [InternedValueMass.value]
        omega
    | mu entry body depth ordinary =>
        have smaller := value_lt body
        simp only [InternedValueMass.value]
        omega
termination_by sizeOf value

/-- The maximum stored-plan depth fits the complete ordered child-list mass. -/
theorem many_le (values : List (Value Symbol Guard)) : manyDepth values ≤ InternedValueMass.values values := by
  cases values with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      have firstBound := value_lt first
      have restBound := many_le rest
      simp only [manyDepth, InternedValueMass.values, Nat.max_le]
      omega
termination_by sizeOf values

/-- The maximum stored-plan depth fits the complete ordered row-list mass. -/
theorem edges_le (rows : List (EdgeValue Symbol Guard)) : edgesDepth rows ≤ InternedValueMass.edges rows := by
  cases rows with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      cases first with
      | mk entry children =>
          have childBound := many_le children
          have restBound := edges_le rest
          simp only [edgesDepth, InternedValueMass.edges, InternedValueMass.edge, Nat.max_le]
          omega
termination_by sizeOf rows
end

/-- One initial causal mass bound gives a fixed degree limit for every stored Mu. -/
theorem stored_bounded (heap : State Symbol Guard) (bound : Nat) (stored : InternedValueMassHeap.Stored bound heap) :
    InternedMuDepthInventory.Bounded heap bound := by
  intro key entry body depth ordinary found
  have whole := stored.nodes key (.mu entry body depth ordinary) found
  have bodyBound := value_lt body
  simp only [InternedValueMass.value] at whole
  omega

end MicroCFTA.InternedValueMassBinderDepth
