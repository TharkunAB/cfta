/-- Class allocation retains the protected root through every fresh variable. -/
theorem suspension_protected (held count : Nat) (before : State Symbol Guard)
    (safe : Safe before) (inside : held < before.counter) (root : IsRoot before.representatives held) :
    Protected held before (suspendedState count before) := by
  induction count generalizing before with
  | zero => exact .refl held before root
  | succ count ih =>
      have first := allocation_protected held none before safe inside root
      exact first.trans (ih (allocated none before)
        ⟨allocation_storage none before safe.1, allocation_live none before safe.1 safe.2⟩
        (by simpa [allocated] using Nat.lt_succ_of_lt inside) first.root)
