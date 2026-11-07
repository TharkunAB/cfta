import MicroCFTA.EnumerationStateFullyIndexValidity

namespace MicroCFTA.EnumerationStateNoPruningIndexValidity

open EnumerationState EnumerationStateIndexValidity EnumerationStateFullyIndexValidity

variable {Symbol Guard : Type}

/-- The default callback preserves the enumeration state in both callback slots. -/
theorem noPruning_preserves_indices :
    OraclePreservesIndices (noPruning : Oracle Symbol Guard Unit) := by
  constructor
  · intro oracleState key node before answer after indexed _ returned
    change Except.ok (answer, after) ∈ [Except.ok ((false, oracleState), before)] at returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (List.mem_singleton.mp returned))
    exact ⟨indexed, Nat.le_refl _⟩
  · intro oracleState key fragment before answer after indexed _ _ returned
    change Except.ok (answer, after) ∈ [Except.ok ((false, oracleState), before)] at returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (List.mem_singleton.mp returned))
    exact ⟨indexed, Nat.le_refl _⟩

/-- The default worker preserves valid references without a callback premise. -/
theorem enumerateFully_default_preserves_indices (graph : Graph Symbol Guard) (fuel : Nat)
    (before after : EnumerationState.State Symbol Guard) (indexed : Indexed before)
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph (fun _ _ => none) noPruning fuel () before)) :
    Indexed after ∧ before.counter ≤ after.counter := by
  exact enumerateFully_preserves_indices graph (fun _ _ => none) noPruning
    noPruning_preserves_indices fuel () before after indexed returned

/-- Initialization discharges the default worker's incoming reference invariant. -/
theorem enumerateFully_default_initial_indices (graph : Graph Symbol Guard) (fuel root : Nat)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph (fun _ _ => none) noPruning fuel ()
        (EnumerationState.initial root))) :
    Indexed after ∧ 1 ≤ after.counter := by
  exact enumerateFully_initial_indices graph (fun _ _ => none) noPruning
    noPruning_preserves_indices fuel root () after returned

end MicroCFTA.EnumerationStateNoPruningIndexValidity
