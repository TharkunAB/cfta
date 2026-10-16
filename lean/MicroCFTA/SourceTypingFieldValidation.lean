import MicroCFTA.SourceTypingRules

/-!
# Runtime field checks for source typing rules

Recursive fields require Subterm. Fixed fields must have another runtime
type, equal to the encoded root constructor's runtime type. These checks
do not establish codec laws or the independent validity of a fixed tree.
-/
namespace MicroCFTA.SourceTypingFieldValidation
open Language SourceTypingRules
variable {Ty Symbol RuntimeType : Type}

/-- The repaired source checker distinguishes recursive fields from fixed values. -/
def fits [DecidableEq RuntimeType] (datatype field : RuntimeType) (encodedType : Term Symbol → RuntimeType) :
    Child Ty Symbol → Bool
  | .subterm _ _ => decide (field = datatype)
  | .value term => decide (field ≠ datatype) && decide (field = encodedType term)

/-- Fixed fields have another runtime type and retain the exact encoded root type. -/
theorem value_iff [DecidableEq RuntimeType] (datatype field : RuntimeType) (encodedType : Term Symbol → RuntimeType)
    (term : Term Symbol) :
    fits (Ty := Ty) datatype field encodedType (.value term) = true ↔
      field ≠ datatype ∧ field = encodedType term := by
  simp [fits]

/-- A recursive field accepts exactly a Subterm declaration, independent of the fixed tree. -/
theorem recursive_iff [DecidableEq RuntimeType] (datatype : RuntimeType) (encodedType : Term Symbol → RuntimeType)
    (child : Child Ty Symbol) : fits datatype datatype encodedType child = true ↔
      ∃ binds typ, child = .subterm binds typ := by
  cases child <;> simp [fits]

/-- An accepted fixed value has an encoded root type other than the target type. -/
theorem fixed_root_other [DecidableEq RuntimeType] (datatype field : RuntimeType) (encodedType : Term Symbol → RuntimeType)
    (term : Term Symbol) (accepted : fits (Ty := Ty) datatype field encodedType (.value term) = true) :
    encodedType term ≠ datatype := by
  obtain ⟨different, same⟩ := (value_iff datatype field encodedType term).mp accepted
  exact same ▸ different

/-- A field of another datatype cannot be treated as a typed recursive subterm. -/
theorem foreign_subterm [DecidableEq RuntimeType] (datatype field : RuntimeType) (encodedType : Term Symbol → RuntimeType)
    (binds : List Ty) (typ : Ty) (different : field ≠ datatype) :
    fits datatype field encodedType (.subterm binds typ) = false := by
  simp [fits, different]

end MicroCFTA.SourceTypingFieldValidation
