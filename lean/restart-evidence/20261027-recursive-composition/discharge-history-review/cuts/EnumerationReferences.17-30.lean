/-- Every listed suspended reference has an allowed variable. -/
def InputsAllowed (allowed : Nat → Prop) (scs : List Suspended) : Prop := ∀ sc ∈ scs, allowed sc.var

/-- Every suspended reference in the store has an allowed variable. -/
def ReferencesAllowed (allowed : Nat → Prop) (state : State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, InputsAllowed allowed (references value)

/-- Descent retains the variable of each input constraint. -/
theorem descend_allowed (allowed : Nat → Prop) (scs : List Suspended) (index : Nat) (inputs : InputsAllowed allowed scs) :
    InputsAllowed allowed (descendScs index scs) := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact inputs original present
