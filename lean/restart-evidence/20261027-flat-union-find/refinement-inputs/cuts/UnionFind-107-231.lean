structure Result where
  representative : Nat
  size : Nat
  forest : Forest

/-- Execute the Haskell lookup with an explicit finite recursion bound. -/
def findRoot : Nat → Forest → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, forest, uv =>
    match forest uv with
    | none => some ⟨uv, 1, put forest uv (.root 1)⟩
    | some (.root size) => some ⟨uv, size, forest⟩
    | some (.parent next) => do
      let found ← findRoot fuel forest next
      some {found with forest := put found.forest uv (.parent found.representative)}

/-- Every successful lookup follows an original path and preserves all original paths. -/
theorem findRoot_correct (fuel : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (result : findRoot fuel forest uv = some found) :
    Reaches forest uv found.representative found.size ∧
      (∀ {other root count}, Reaches forest other root count → Reaches found.forest other root count) := by
  induction fuel generalizing forest uv found with
  | zero => simp [findRoot] at result
  | succ fuel ih =>
    cases lookup : forest uv with
    | none =>
      simp [findRoot, lookup] at result
      subst found
      refine ⟨.root (by simp [read, lookup]), ?_⟩
      intro other root count path
      exact reaches_congr (fun other => (insert_missing lookup other).symm) path
    | some entry =>
      cases entry with
      | root size =>
        simp [findRoot, lookup] at result
        subst found
        exact ⟨.root (by simp [read, lookup]), fun path => path⟩
      | parent next =>
        cases recursive : findRoot fuel forest next with
        | none => simp [findRoot, lookup, recursive] at result
        | some earlier =>
          simp [findRoot, lookup, recursive] at result
          subst found
          obtain ⟨tail, preserved⟩ := ih forest next earlier recursive
          have path : Reaches forest uv earlier.representative earlier.size :=
            .parent (by simp [read, lookup]) tail
          have different : uv ≠ earlier.representative := by
            intro same
            have terminal := reaches_terminal path
            simp [← same, read, lookup] at terminal
          exact ⟨path, fun original => compress_preserves (preserved path) different (preserved original)⟩

/-- Every finite parent path gives a successful bounded execution. -/
theorem findRoot_terminates (path : Reaches forest uv representative size) :
    ∃ fuel found, findRoot fuel forest uv = some found := by
  induction path with
  | @root uv size lookup =>
    cases actual : forest uv with
    | none => exact ⟨1, ⟨uv, 1, put forest uv (.root 1)⟩, by simp [findRoot, actual]⟩
    | some entry =>
      have same : entry = .root size := by simpa [read, actual] using lookup
      subst entry
      exact ⟨1, ⟨uv, size, forest⟩, by simp [findRoot, actual]⟩
  | @parent uv next representative size lookup tail ih =>
    obtain ⟨fuel, found, result⟩ := ih
    cases actual : forest uv with
    | none => simp [read, actual] at lookup
    | some entry =>
      have same : entry = .parent next := by simpa [read, actual] using lookup
      subst entry
      exact ⟨fuel + 1, {found with forest := put found.forest uv (.parent found.representative)},
        by simp [findRoot, actual, result]⟩

/-- Additional execution fuel does not change a successful result. -/
theorem findRoot_moreFuel (fuel extra : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (result : findRoot fuel forest uv = some found) :
    findRoot (fuel + extra) forest uv = some found := by
  induction fuel generalizing forest uv found with
  | zero => simp [findRoot] at result
  | succ fuel ih =>
    rw [Nat.succ_add]
    cases lookup : forest uv with
    | none => simpa [findRoot, lookup] using result
    | some entry =>
      cases entry with
      | root size => simpa [findRoot, lookup] using result
      | parent next =>
        cases recursive : findRoot fuel forest next with
        | none => simp [findRoot, lookup, recursive] at result
        | some earlier =>
          have extended := ih forest next earlier recursive
          simpa [findRoot, lookup, extended, recursive] using result

/-- Every variable in a valid forest has a finite path to a root. -/
def Total (forest : Forest) : Prop := ∀ uv, ∃ representative size, Reaches forest uv representative size

/-- Successful lookup preserves termination of all later lookups. -/
theorem findRoot_total (valid : Total forest)
    (result : findRoot fuel forest uv = some found) : Total found.forest := by
  intro other
  obtain ⟨root, count, path⟩ := valid other
  exact ⟨root, count, (findRoot_correct _ _ _ _ result).2 path⟩

/-- A total forest admits no new root paths after a successful lookup. -/
theorem findRoot_reaches_iff (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (other root count : Nat) :
    Reaches found.forest other root count ↔ Reaches forest other root count := by
  have preserves : ∀ {a r n}, Reaches forest a r n → Reaches found.forest a r n :=
    (findRoot_correct _ _ _ _ result).2
  constructor
  · intro after
    obtain ⟨oldRoot, oldCount, before⟩ := valid other
    obtain ⟨hr, hc⟩ := reaches_unique (preserves before) after
    simpa only [hr, hc] using before
  · exact preserves

/-- Two variables belong to one class when their finite paths reach one root. -/
def SameClass (forest : Forest) (left right : Nat) : Prop :=
  ∃ representative size, Reaches forest left representative size ∧ Reaches forest right representative size

/-- Path compression preserves the exact equivalence classes. -/
theorem findRoot_classes (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (left right : Nat) :
    SameClass found.forest left right ↔ SameClass forest left right := by
  simp only [SameClass, findRoot_reaches_iff valid result]
