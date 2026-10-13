import MicroCFTA.InternedProfileEquivalence
import MicroCFTA.InternedRootProfileLists
import MicroCFTA.InternedUnionNormalForm

/-!
# Literal root-reference erasure on actual atomic operands

The source root filter removes only direct reference operands. Actual
stored unions have atomic members. On those members, filtering the records
therefore erases exactly the same names from their pure root profile.
-/
namespace MicroCFTA.InternedProfileErasure
open InternedConstructorTemplates InternedRootProfile InternedUnionNormalForm
open InternedBinderProtocol (Reference)

/-- Remove one literal name from a pure profile and retain opacity. -/
def erase (name : Reference) (value : Profile) : Profile := value.map (List.filter (· != name))

/-- Literal erasure commutes with profile union. -/
theorem erase_combine (name : Reference) (first second : Profile) :
    erase name (combine first second) = combine (erase name first) (erase name second) := by
  cases first <;> cases second <;> simp [erase, combine, List.filter_append]

/-- Filtering actual atomic source operands erases precisely their literal root names. -/
theorem many_remove (name : Reference) (values : List (Value Symbol Guard))
    (atomic : ∀ value ∈ values, Atomic value) :
    many (values.filter (fun value => value.referenceOf != .ref name)) = erase name (many values) := by
  induction values with
  | nil => simp [many, erase]
  | cons first rest ih =>
      have head := atomic first (by simp)
      have tail : ∀ value ∈ rest, Atomic value := fun value member => atomic value (by simp [member])
      rw [many, erase_combine]
      rw [← ih tail]
      cases first with
      | union => contradiction
      | empty =>
          simp only [Value.referenceOf, reduceCtorEq, bne_iff_ne, ne_eq, not_false_eq_true, List.filter_cons_of_pos, profile, erase, Option.map_some, List.filter_nil, many]
      | reference other =>
          by_cases same : other = name
          · subst other
            simp only [List.filter_cons]
            simp [Value.referenceOf, profile, erase]
            generalize many _ = remaining
            cases remaining <;> rfl
          · simp [Value.referenceOf, profile, erase, many, same]
      | node => simp [Value.referenceOf, profile, erase, many, combine]
      | mu => simp [Value.referenceOf, profile, erase, many, combine]

/-- An absent selected literal does not change a pure or opaque profile. -/
theorem erase_absent (name : Reference) (value : Profile) (absent : name ∉ value.getD []) : erase name value = value := by
  cases value with
  | none => rfl
  | some names =>
      simp only [erase, Option.map_some, Option.some.injEq]
      apply List.filter_eq_self.mpr
      intro other member
      have different : other ≠ name := by intro same; exact absent (same ▸ member)
      simpa using different

end MicroCFTA.InternedProfileErasure
