import MicroCFTA.SourceCurrentStoredFilteredProfile

/-!
# Deletion of original root reference alternatives

Deletion follows original root unions. It tests each original bare
reference before profile assignment. It does not delete names introduced
by a replacement or exposed by stored Mu reconstruction. The actual self
filter has a separate exception for a standalone reference.
-/
namespace MicroCFTA.SourceCurrentStoredRootDeletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combine combineMany)
open InternedBinderProtocol (Reference)
open InternedStoredMuOrigins (Normal)
open InternedNestedProvenance (Values)
open SourceCurrentStoredProfileFunction (denote)

mutual
/-- Delete selected original root references before assigning profiles. -/
def deleted (cuts : Reference → Bool) (value : Value Symbol Guard) (assignment : Reference → Profile) : Profile :=
  match value with
  | .empty => some []
  | .reference name => if cuts name then some [] else assignment name
  | .union _ members _ _ => deletedMany cuts members assignment
  | _ => denote value assignment
termination_by sizeOf value

/-- Combine deletion observations of the original ordered alternatives. -/
def deletedMany (cuts : Reference → Bool) (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) : Profile :=
  match values with
  | [] => some []
  | first :: rest => combine (deleted cuts first assignment) (deletedMany cuts rest assignment)
termination_by sizeOf values
end

mutual
/-- An empty deletion predicate gives the full stored assigned profile. -/
theorem uncut (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    deleted (fun _ => false) value assignment = denote value assignment := by
  cases value with
  | empty => rw [deleted]; exact (SourceCurrentStoredProfileFunction.empty assignment).symm
  | reference name =>
      simp only [deleted,Bool.false_eq_true,ite_false]
      exact (SourceCurrentStoredProfileFunction.reference name assignment).symm
  | node | mu => rw [deleted]
  | union entry members depth free =>
      rw [deleted,uncut_many members assignment state normal (fun child member => available.children child member)]
      exact (SourceCurrentStoredProfileComposition.union entry members depth free assignment state normal available).symm
termination_by sizeOf value

/-- Empty deletion combines the full profiles of every original alternative. -/
theorem uncut_many (values : List (Value Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Values state values) :
    deletedMany (fun _ => false) values assignment = combineMany (values.map (fun value => denote value assignment)) := by
  cases values with
  | nil => rw [deletedMany]; rfl
  | cons first rest =>
      rw [deletedMany,uncut first assignment state normal (available first List.mem_cons_self),
        uncut_many rest assignment state normal (fun child member => available child (List.mem_cons_of_mem _ member))]
      rfl
termination_by sizeOf values
end

end MicroCFTA.SourceCurrentStoredRootDeletion
