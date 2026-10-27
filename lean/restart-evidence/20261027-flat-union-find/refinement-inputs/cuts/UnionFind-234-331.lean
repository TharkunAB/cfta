def link (forest : Forest) (loser winner loserSize winnerSize : Nat) : Forest :=
  put (put forest loser (.parent winner)) winner (.root (loserSize + winnerSize))

/-- The root selected after linking two different classes. -/
def redirect (loser winner root : Nat) : Nat := if root = loser then winner else root

/-- Only the two merged classes receive the added root size. -/
def mergedSize (loser winner loserSize winnerSize root size : Nat) : Nat :=
  if root = loser ∨ root = winner then loserSize + winnerSize else size

/-- Linking two roots changes precisely their representatives and stored sizes. -/
theorem link_reaches
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (path : Reaches forest uv representative size) :
    Reaches (link forest loser winner loserSize winnerSize) uv
      (redirect loser winner representative)
      (mergedSize loser winner loserSize winnerSize representative size) := by
  have winnerPath : Reaches (link forest loser winner loserSize winnerSize) winner winner
      (loserSize + winnerSize) := .root (read_put_same ..)
  have loserPath : Reaches (link forest loser winner loserSize winnerSize) loser winner
      (loserSize + winnerSize) := .parent
        (by simp [link, different]) winnerPath
  induction path with
  | @root uv size lookup =>
    by_cases isLoser : uv = loser
    · subst uv
      simpa [redirect, mergedSize] using loserPath
    · by_cases isWinner : uv = winner
      · subst uv
        simpa [redirect, mergedSize, Ne.symm different] using winnerPath
      · simp only [redirect, mergedSize, isLoser, isWinner, or_self, ↓reduceIte]
        exact .root (by simp [link, isLoser, isWinner, lookup])
  | @parent uv next representative size lookup tail ih =>
    have notLoser : uv ≠ loser := by
      intro same; subst uv; rw [loserRoot] at lookup; cases lookup
    have notWinner : uv ≠ winner := by
      intro same; subst uv; rw [winnerRoot] at lookup; cases lookup
    exact .parent (by simp [link, notLoser, notWinner, lookup]) ih

/-- Linking two distinct roots preserves termination throughout the forest. -/
theorem link_total (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner) :
    Total (link forest loser winner loserSize winnerSize) := by
  intro uv
  obtain ⟨root, size, path⟩ := valid uv
  exact ⟨_, _, link_reaches loserRoot winnerRoot different path⟩

/-- Equality of representatives characterizes class membership. -/
theorem sameClass_iff_roots (left : Reaches forest x root₁ size₁)
    (right : Reaches forest y root₂ size₂) : SameClass forest x y ↔ root₁ = root₂ := by
  constructor
  · rintro ⟨root, size, hx, hy⟩
    exact (reaches_unique left hx).1.trans (reaches_unique right hy).1.symm
  · intro same
    subst root₂
    have sizes : size₁ = size₂ := by
      have equality := (reaches_terminal left).symm.trans (reaches_terminal right)
      cases equality
      rfl
    subst size₂
    exact ⟨root₁, size₁, left, right⟩

/-- A root redirect identifies only the two selected roots. -/
theorem redirect_eq_iff (loser winner left right : Nat) :
    redirect loser winner left = redirect loser winner right ↔
      left = right ∨ (left = loser ∧ right = winner) ∨ (left = winner ∧ right = loser) := by
  simp only [redirect]
  split <;> split <;> grind

/-- Linking merges exactly the selected equivalence classes and no others. -/
theorem link_classes (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (left right : Nat) :
    SameClass (link forest loser winner loserSize winnerSize) left right ↔
      SameClass forest left right ∨
      (SameClass forest left loser ∧ SameClass forest right winner) ∨
      (SameClass forest left winner ∧ SameClass forest right loser) := by
  obtain ⟨lr, ls, hl⟩ := valid left
  obtain ⟨rr, rs, hr⟩ := valid right
  rw [sameClass_iff_roots (link_reaches loserRoot winnerRoot different hl)
    (link_reaches loserRoot winnerRoot different hr)]
  rw [sameClass_iff_roots hl hr,
    sameClass_iff_roots hl (.root loserRoot), sameClass_iff_roots hr (.root winnerRoot),
    sameClass_iff_roots hl (.root winnerRoot), sameClass_iff_roots hr (.root loserRoot)]
  exact redirect_eq_iff ..

/-- Execute both lookups and merge their classes by the stored size comparison. -/
def union (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) : Option Forest := do
  let first ← findRoot leftFuel forest left
  let second ← findRoot rightFuel first.forest right
  if first.representative = second.representative then
    some second.forest
  else if first.size < second.size then
    some (link second.forest first.representative second.representative first.size second.size)
  else
