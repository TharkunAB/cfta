def Canonical (state : State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, ValidSuspended (references value)

/-- The initialized root has no suspended constraints. -/
theorem initial_canonical (root : Nat) : Canonical (initial root : State Symbol Guard) := by
  simp [Canonical, initial, references, ValidSuspended]

/-- Replacing one slot preserves canonical tries when its new payload is canonical. -/
theorem set_canonical (uv : Nat) (value : UVarValue Symbol) (state : State Symbol Guard)
    (valid : Canonical state) (newValue : ValidSuspended (references value)) :
    Canonical {state with values := state.values.set uv value} := by
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid stored old
  · simpa [same] using newValue

/-- A successful source slot write preserves canonical tries. -/
theorem setValue_canonical (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (valid : Canonical before) (newValue : ValidSuspended (references value))
    (success : Success (setValue uv value) before () after) : Canonical after := by
  obtain rfl := (modify_success _ before after).mp success
  exact set_canonical uv value before valid newValue

/-- A raw read retains every trie and exposes a canonical payload. -/
theorem rawValue_canonical (uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : Canonical before) (success : Success (rawValue uv) before value after) :
    Canonical after ∧ ValidSuspended (references value) := by
  obtain ⟨stored, same⟩ := (rawValue_success uv before after value).mp success
  subst after
  exact ⟨valid, valid value (List.mem_of_getElem? stored)⟩

/-- Representative compression changes no stored trie. -/
theorem representative_canonical (fuel uv root : Nat) (before after : State Symbol Guard)
    (valid : Canonical before) (success : Success (representative fuel uv) before root after) : Canonical after := by
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact valid

/-- A representative read exposes canonical suspended constraints. -/
theorem getValue_canonical (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : Canonical before) (success : Success (getValue fuel uv) before value after) :
    Canonical after ∧ ValidSuspended (references value) := by
  obtain ⟨found, _, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  exact ⟨valid, valid value (List.mem_of_getElem? stored)⟩
