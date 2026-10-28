      exact total

/-- Every actual shallow candidate retains old carriers, including empty rejection. -/
theorem cache_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (safe : Safe before.core) (references : ReferencesCarry before.core)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none => simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact ⟨safe.1.total, .refl _, references⟩
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              have facts := rows_carriers heap fuel scs value before [(fragment, reached)]
                safe references prepared fragment reached (by simp)
              exact ⟨rows_total heap fuel scs value before [(fragment, reached)] safe.1.total
                prepared fragment reached (by simp), facts.1, facts.2.1⟩
          | cons row rest => simp only [prepared, reduceCtorEq] at observed
