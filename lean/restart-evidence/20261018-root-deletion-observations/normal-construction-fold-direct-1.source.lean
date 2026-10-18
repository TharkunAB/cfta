import MicroCFTA.InternedProfileSemantics

/-!
# Pure profile fold laws

These laws preserve profile opacity and root-name membership.
They do not require a constructor heap or source execution.
-/
namespace MicroCFTA.SourceCurrentProfileFold
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combineMany)
open InternedBinderProtocol (Reference)

/-- Appending the empty pure profile does not change the result. -/
theorem combine_empty_right (value : Profile) :
    InternedProfileSemantics.combine value (some []) = value := by
  cases value <;> simp [InternedProfileSemantics.combine]

private theorem combine_assoc (first second third : Profile) :
    InternedProfileSemantics.combine (InternedProfileSemantics.combine first second) third =
      InternedProfileSemantics.combine first (InternedProfileSemantics.combine second third) := by
  cases first <;> cases second <;> cases third <;> simp [InternedProfileSemantics.combine,List.append_assoc]

/-- Profile folding preserves source grouping. -/
theorem fold_append (first second : List Profile) : combineMany (first ++ second) =
    InternedProfileSemantics.combine (combineMany first) (combineMany second) := by
  induction first with
  | nil =>
      cases found : combineMany second <;>
        simp [combineMany,InternedProfileSemantics.combine,found]
  | cons first rest ih => simp only [List.cons_append,combineMany,ih,combine_assoc]

private theorem fold_none (values : List Profile) : combineMany values = none ↔ ∃ value ∈ values, value = none := by
  induction values with
  | nil => simp [combineMany]
  | cons first rest ih =>
      cases first <;> cases restProfile : combineMany rest <;>
        simp_all [combineMany,InternedProfileSemantics.combine]

private theorem fold_member (values : List Profile) (names : List Reference)
    (pure : combineMany values = some names) (name : Reference) :
    name ∈ names ↔ ∃ value ∈ values, name ∈ value.getD [] := by
  induction values generalizing names with
  | nil => simp_all [combineMany]
  | cons first rest ih =>
      cases first with
      | none => simp [combineMany,InternedProfileSemantics.combine] at pure
      | some firstNames =>
          cases restProfile : combineMany rest with
          | none => simp [combineMany,InternedProfileSemantics.combine,restProfile] at pure
          | some restNames =>
              have same : firstNames ++ restNames = names := by
                simpa only [combineMany,restProfile,InternedProfileSemantics.combine,Option.some.injEq] using pure
              subst names
              simp only [List.mem_append,ih restNames restProfile,List.mem_cons,exists_eq_or_imp,Option.getD_some]

/-- Profile folding depends only on the set of complete input profiles. -/
theorem fold_equiv (first second : List Profile) (same : ∀ value, value ∈ first ↔ value ∈ second) :
    Equivalent (combineMany first) (combineMany second) := by
  have opacity : combineMany first = none ↔ combineMany second = none := by
    rw [fold_none,fold_none]
    exact exists_congr fun value => and_congr_left fun _ => same value
  refine ⟨opacity,?_⟩
  intro name
  cases one : combineMany first with
  | none => rw [opacity.mp one]
  | some firstNames =>
      cases two : combineMany second with
      | none => have impossible := opacity.mpr two; simp [one] at impossible
      | some secondNames =>
          simp only [Option.getD_some]
          rw [fold_member first firstNames one,fold_member second secondNames two]
          exact exists_congr fun value => and_congr_left fun _ => same value

end MicroCFTA.SourceCurrentProfileFold
