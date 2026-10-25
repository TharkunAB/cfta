@[simp, grind =] theorem mem_flatMap {f : α → List β} {b} {l : List α} : b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {l : List α} {f : α → List β} :
    b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a := mem_flatMap.1
