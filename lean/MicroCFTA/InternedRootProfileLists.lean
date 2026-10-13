import MicroCFTA.InternedRootProfile
import MicroCFTA.InternedUnionRetention

/-!
# Root profiles through source operand lists

Flattening preserves the complete root profile. Identity deduplication
preserves opacity and the set of references for actual resident operands.
-/
namespace MicroCFTA.InternedRootProfileLists
open InternedConstructorTemplates InternedRootProfile InternedRecordCoherence
open InternedFreshProbeKeys InternedUnionRetention InternedProbeProvenance
open InternedBinderProtocol (Reference)

/-- Appending an empty pure profile has no effect. -/
theorem combine_empty_right (value : Profile) : combine value (some []) = value := by
  cases value <;> simp [combine]

/-- Root profile combination preserves source grouping. -/
theorem combine_assoc (first second third : Profile) :
    combine (combine first second) third = combine first (combine second third) := by
  cases first <;> cases second <;> cases third <;> simp [combine, List.append_assoc]

/-- Appended source operand lists combine their profiles. -/
theorem many_append (first second : List (Value Symbol Guard)) :
    many (first ++ second) = combine (many first) (many second) := by
  induction first with
  | nil =>
      simp only [List.nil_append, many]
      cases many second <;> simp [combine]
  | cons first rest ih => simp only [List.cons_append, many, ih, combine_assoc]

/-- Flattening one source union preserves its root profile. -/
theorem members_profile (value : Value Symbol Guard) : many (unionMembers value) = profile value := by
  cases value <;> simp [unionMembers, profile, many, combine_empty_right]

/-- Flattening all original operands preserves the exact profile list before deduplication. -/
theorem flatten_profile (values : List (Value Symbol Guard)) : many (values.flatMap unionMembers) = many values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.flatMap_cons, many_append, members_profile, ih, many]

/-- A combined profile is opaque exactly when one source operand is opaque. -/
theorem many_none_iff (values : List (Value Symbol Guard)) :
    many values = none ↔ ∃ value ∈ values, profile value = none := by
  induction values with
  | nil => simp [many]
  | cons first rest ih =>
      cases firstProfile : profile first <;> cases restProfile : many rest <;>
        simp_all [many, combine]

/-- A pure combined profile retains precisely the references in its original operands. -/
theorem many_some_member (values : List (Value Symbol Guard)) (names : List Reference)
    (pure : many values = some names) (name : Reference) :
    name ∈ names ↔ ∃ value ∈ values, name ∈ (profile value).getD [] := by
  induction values generalizing names with
  | nil => simp_all [many]
  | cons first rest ih =>
      cases firstProfile : profile first <;> cases restProfile : many rest <;>
        simp only [many, firstProfile, restProfile, combine, reduceCtorEq, Option.some.injEq] at pure
      case some.some firstNames restNames =>
        subst names
        simp only [List.mem_append, ih restNames restProfile, List.mem_cons, exists_eq_or_imp,
          firstProfile, Option.getD_some]

/-- Profiles depend on the set of complete operands, not their duplicate count or order. -/
theorem many_equivalent (first second : List (Value Symbol Guard))
    (same : ∀ value, value ∈ first ↔ value ∈ second) : Equivalent (many first) (many second) := by
  have opacity : many first = none ↔ many second = none := by
    simp only [many_none_iff]
    exact exists_congr fun value => and_congr_left fun _ => same value
  refine ⟨opacity, ?_⟩
  intro name
  cases left : many first with
  | none => rw [opacity.mp left]
  | some leftNames =>
      cases right : many second with
      | none => have := opacity.mpr right; simp [left] at this
      | some rightNames =>
          simp only [Option.getD_some]
          rw [many_some_member first leftNames left, many_some_member second rightNames right]
          exact exists_congr fun value => and_congr_left fun _ => same value

/-- Actual resident identity deduplication preserves opacity and every root reference. -/
theorem distinct_equivalent (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (resident : ∀ value ∈ values, Resident state value) :
    Equivalent (many (distinctNodes values)) (many values) :=
  many_equivalent _ _ (fun value => ⟨distinctNodes_member values value,
    distinctNodes_retains state coherent values resident value⟩)

end MicroCFTA.InternedRootProfileLists
