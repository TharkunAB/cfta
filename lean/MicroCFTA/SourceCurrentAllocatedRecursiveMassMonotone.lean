import MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace

/-!
# Monotone checked-query resource schedules

Larger initial payload bounds retain the one-step mass and allocation bounds.
Additional checked instructions retain both accumulated schedules. These laws
replace an actual prefix length by a proved initial instruction budget.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
open SourceCurrentAllocatedRecursiveMassTrace

private theorem evolve_width_mono (count : Nat) {first last : Nat}
    (enough : first ≤ last) (bound : Nat) :
    InternedFreshOrdinaryUniformMass.evolve first count bound ≤
      InternedFreshOrdinaryUniformMass.evolve last count bound := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    exact Nat.mul_le_mul (Nat.add_le_add_right enough 3) (Nat.add_le_add_right ih 1)

private theorem optional_ceiling_mono {first last : Nat} (enough : first ≤ last) :
    SourceCurrentAllocatedRecursiveMassBudget.ceiling first ≤
      SourceCurrentAllocatedRecursiveMassBudget.ceiling last := by
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 3) enough
  have count : SourceCurrentAllocatedRecursiveMassBudget.growthSteps first ≤
      SourceCurrentAllocatedRecursiveMassBudget.growthSteps last := by
    unfold SourceCurrentAllocatedRecursiveMassBudget.growthSteps
    omega
  exact Nat.le_trans (evolve_width_mono _ enough first)
    (Nat.le_trans (InternedFreshOrdinaryUniformMass.evolve_count_mono last count first)
      (InternedFreshOrdinaryUniformMass.evolve_mono last _ enough))

/-- A larger initial mass bound retains the common one-step store bound. -/
theorem ceiling_mono {first last : Nat} (enough : first ≤ last) : ceiling first ≤ ceiling last := by
  have width := SourceRecursiveIntersectionWorkMass.inflate_width (Nat.mul_le_mul enough enough) first
  have bound := InternedFreshOrdinaryResultMass.inflate_mono (last * last) enough
  have optional := optional_ceiling_mono enough
  unfold ceiling listLimit
  exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_trans width bound) (Nat.le_max_left _ _),
    Nat.le_trans optional (Nat.le_max_right _ _)⟩

/-- A larger initial mass bound retains the one-step constructor charge. -/
theorem charge_mono {first last : Nat} (enough : first ≤ last) : charge first ≤ charge last := by
  unfold charge SourceCurrentAllocatedRecursiveMassBudget.charge
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by decide : 1 ≤ 3) enough)) 1

/-- A fixed instruction schedule retains a larger initial payload bound. -/
theorem massAfter_bound_mono (count : Nat) {first last : Nat} (enough : first ≤ last) :
    massAfter count first ≤ massAfter count last := by
  induction count generalizing first last with
  | zero => exact enough
  | succ count ih => exact ih (ceiling_mono enough)

/-- Additional instructions retain the earlier scheduled payload bound. -/
theorem massAfter_count_mono {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    massAfter first bound ≤ massAfter last bound := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [massAfter_add]
  exact massAfter_ge extra _

/-- Larger initial bounds and instruction counts retain the scheduled payload bound. -/
theorem massAfter_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    massAfter firstCount firstBound ≤ massAfter lastCount lastBound :=
  Nat.le_trans (massAfter_count_mono counts firstBound) (massAfter_bound_mono lastCount bounds)

/-- A fixed instruction schedule retains the constructor credit at a larger initial bound. -/
theorem credit_bound_mono (count : Nat) {first last : Nat} (enough : first ≤ last) :
    credit count first ≤ credit count last := by
  induction count generalizing first last with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.add_le_add (charge_mono enough) (ih (ceiling_mono enough))

/-- Additional instructions retain the earlier accumulated constructor credit. -/
theorem credit_count_mono {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    credit first bound ≤ credit last bound := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [credit_add]
  exact Nat.le_add_right _ _

/-- Larger initial bounds and instruction counts retain the accumulated constructor credit. -/
theorem credit_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    credit firstCount firstBound ≤ credit lastCount lastBound :=
  Nat.le_trans (credit_count_mono counts firstBound) (credit_bound_mono lastCount bounds)

end MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
