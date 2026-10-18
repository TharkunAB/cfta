import MicroCFTA.SourceCurrentSourceEmptyAbstraction
import MicroCFTA.SourceCurrentStoredRootDeletion

/-!
# Canonical Empty observations of stored profiles

Stored denotation preserves pointwise Empty agreement of assignments.
The proof uses the same full stored encoding on both sides. Original-root
deletion has the same property. It cuts original references before any
assignment and does not cut names later exposed by a Mu or replacement.
-/
namespace MicroCFTA.SourceCurrentStoredProfileEmptyProjection
open InternedConstructorTemplates
open InternedRootProfile (Profile profile)
open InternedProfileSemantics (isEmpty combine)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted deletedMany)

/-- Replace every assigned profile by its canonical Empty or opaque representative. -/
def canonical (assignment : Reference → Profile) (name : Reference) : Profile :=
  if isEmpty (assignment name) then some [] else none

private theorem canonical_empty (assignment : Reference → Profile) (name : Reference) :
    isEmpty (assignment name) = isEmpty (canonical assignment name) := by
  unfold canonical
  cases isEmpty (assignment name) <;> rfl

/-- The same stored plan preserves pointwise Empty agreement of its assignments. -/
theorem denote_empty (value : Value Symbol Guard) (first second : Reference → Profile)
    (same : ∀ name, isEmpty (first name) = isEmpty (second name)) :
    isEmpty (denote value first) = isEmpty (denote value second) := by
  unfold denote
  apply SourceCurrentSourceEmptyAbstraction.same_empty
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro leaf _
  cases leaf with
  | reference name => exact same name
  | empty | node | union | mu => rfl

private theorem combine_empty (first second : Profile) :
    isEmpty (combine first second) = (isEmpty first && isEmpty second) := by
  cases first with
  | none => cases second <;> rfl
  | some first =>
      cases second with
      | none => cases first <;> rfl
      | some second => cases first <;> cases second <;> rfl

mutual
/-- Original-root deletion preserves pointwise Empty agreement under any fixed cuts. -/
theorem deleted_empty (cuts : Reference → Bool) (value : Value Symbol Guard)
    (first second : Reference → Profile)
    (same : ∀ name, isEmpty (first name) = isEmpty (second name)) :
    isEmpty (deleted cuts value first) = isEmpty (deleted cuts value second) := by
  cases value with
  | empty => rfl
  | reference name =>
      rw [deleted,deleted]
      cases cuts name with
      | false => exact same name
      | true => rfl
  | node | mu => exact denote_empty _ first second same
  | union entry members depth free =>
      exact deletedMany_empty cuts members first second same
termination_by sizeOf value

private theorem deletedMany_empty (cuts : Reference → Bool) (values : List (Value Symbol Guard))
    (first second : Reference → Profile)
    (same : ∀ name, isEmpty (first name) = isEmpty (second name)) :
    isEmpty (deletedMany cuts values first) = isEmpty (deletedMany cuts values second) := by
  cases values with
  | nil => rfl
  | cons value rest =>
      rw [deletedMany,deletedMany,combine_empty,combine_empty,
        deleted_empty cuts value first second same,deletedMany_empty cuts rest first second same]
termination_by sizeOf values
end

/-- Canonical assignment preserves the complete stored denotation's Empty decision. -/
theorem denote_canonical (value : Value Symbol Guard) (assignment : Reference → Profile) :
    isEmpty (denote value assignment) = isEmpty (denote value (canonical assignment)) :=
  denote_empty value assignment (canonical assignment) (canonical_empty assignment)

/-- Canonical assignment preserves Empty after arbitrary original-root deletion. -/
theorem deleted_canonical (cuts : Reference → Bool) (value : Value Symbol Guard)
    (assignment : Reference → Profile) :
    isEmpty (deleted cuts value assignment) = isEmpty (deleted cuts value (canonical assignment)) :=
  deleted_empty cuts value assignment (canonical assignment) (canonical_empty assignment)

end MicroCFTA.SourceCurrentStoredProfileEmptyProjection
