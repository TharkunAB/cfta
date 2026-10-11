import MicroCFTA.Probability
import MicroCFTA.Sparse

/-!
# Transport sizes and masses through pay

A finite grouped constructor increments every member size. Its retained mass
series must move to the same new sizes. The rebased source has two such paths:
`Types.payGroupsWith` and `Compile.compileOpenNode.labelBucket`.
-/

namespace MicroCFTA.SizeTransport
open Probability

/-- One size, relative member weight, and value. -/
abbrev Members (α : Type) := List (Nat × Rat × α)

/-- Select one size class, keeping its member weights. -/
def atSize (size : Nat) : Members α → Distribution α
  | [] => []
  | (found, mass, value) :: rest =>
      if found = size then (mass, value) :: atSize size rest else atSize size rest

/-- Add one to every member size without changing its rank or weight. -/
def pay (members : Members α) : Members α :=
  members.map fun (size, mass, value) => (size + 1, mass, value)

/-- Shift every retained class mass by the same amount. -/
def payMasses (masses : Sparse.Series Rat) : Sparse.Series Rat :=
  masses.map fun (size, mass) => (size + 1, mass)

/-- A paid size class is exactly the corresponding original size class. -/
theorem atSize_pay (members : Members α) (size : Nat) :
    atSize (size + 1) (pay members) = atSize size members := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨found, mass, value⟩
      simp only [pay, List.map_cons, atSize, Nat.add_right_cancel_iff]
      split <;> simp_all [pay]

/-- A pay has no member of size zero. -/
theorem atSize_pay_zero (members : Members α) : atSize 0 (pay members) = [] := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨found, mass, value⟩
      simpa [pay, atSize] using ih

/-- Retained class mass follows the same size shift as the members. -/
theorem coefficient_pay (masses : Sparse.Series Rat) (size : Nat) :
    Sparse.coefficient (payMasses masses) (size + 1) = Sparse.coefficient masses size := by
  induction masses with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨found, mass⟩
      simp only [payMasses, List.map_cons, Sparse.coefficient, Nat.add_right_cancel_iff]
      rw [show Sparse.coefficient (List.map (fun (size, mass) => (size + 1, mass)) rest) (size + 1) =
        Sparse.coefficient rest size from ih]

/-- The shifted mass series has zero mass at size zero. -/
theorem coefficient_pay_zero (masses : Sparse.Series Rat) : Sparse.coefficient (payMasses masses) 0 = 0 := by
  induction masses with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨found, mass⟩
      simpa [payMasses, Sparse.coefficient, Rat.zero_add] using ih

/-- Stored class masses equal the sum of the relative weights of their members. -/
def Coherent (members : Members α) (masses : Sparse.Series Rat) : Prop :=
  ∀ size, Sparse.coefficient masses size = total (atSize size members)

/-- Paying both members and their mass series preserves their correspondence. -/
theorem pay_coherent (members : Members α) (masses : Sparse.Series Rat)
    (coherent : Coherent members masses) : Coherent (pay members) (payMasses masses) := by
  intro size
  cases size with
  | zero => rw [coefficient_pay_zero, atSize_pay_zero]; rfl
  | succ size => rw [coefficient_pay, atSize_pay]; exact coherent size

/-- Paying a constructor preserves the conditional distribution in the shifted class. -/
theorem pay_class_probability (members : Members α) (size : Nat) (event : α → Bool) :
    eventMass event (normalize (atSize (size + 1) (pay members))) =
      eventMass event (normalize (atSize size members)) := by
  rw [atSize_pay]

/-- Keeping old class keys after a pay breaks the stored mass invariant. -/
theorem stale_mass_counterexample :
    Coherent ([(1, 1, true)] : Members Bool) [(1, 1)] ∧
      ¬ Coherent (pay ([(1, 1, true)] : Members Bool)) [(1, 1)] := by
  constructor
  · intro size
    by_cases same : size = 1
    · subst size; decide +kernel
    · simp [Sparse.coefficient, atSize, Ne.symm same, total, Rat.zero_add]
  · intro coherent
    have bad := coherent 2
    have impossible : ¬ (Sparse.coefficient ([(1, 1)] : Sparse.Series Rat) 2 =
        total (atSize 2 (pay ([(1, 1, true)] : Members Bool)))) := by decide +kernel
    exact impossible bad

end MicroCFTA.SizeTransport
