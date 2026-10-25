
/-- Each retained child is available independently of whether its parent later survives normalization. -/
theorem Available.children (available : Available state value) : ∀ child ∈ children value, Available state child := by
