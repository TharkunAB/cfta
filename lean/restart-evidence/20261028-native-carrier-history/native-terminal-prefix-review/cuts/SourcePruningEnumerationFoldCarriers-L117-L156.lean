      ReferencesCarry after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid

/-- The actual adapter retains the old carrier state or its actual singleton state. -/
theorem adapt_carriers
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw} (total : UnionFind.Total before.core.representatives)
    (references : ReferencesCarry before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] →
      returned.representatives = before.core.representatives ∧
        UnionFind.Total returned.representatives ∧ PreservesCarriers before.core returned ∧ ReferencesCarry returned)
    (adapted : adapt heap before source target raw = some after) :
    after.core.representatives = before.core.representatives ∧
      UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  cases raw with
  | nil =>
      simp only [adapt, Option.some.injEq] at adapted
      subst after
      exact ⟨rfl, total, .refl before.core, references⟩
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          rcases payload with ⟨ignored, returned⟩
          cases ignored
          cases rest with
          | cons next later => simp only [adapt] at adapted; cases adapted
          | nil =>
              have returnedValid := rows returned rfl
              by_cases same : source = target
              · simp only [adapt, same, ↓reduceIte, Option.some.injEq] at adapted
                subst after
                exact ⟨rfl, total, .refl before.core, references⟩
              · cases stored : before.core.values[source]? with
                | none =>
                    simp only [adapt, same, ↓reduceIte, stored] at adapted
