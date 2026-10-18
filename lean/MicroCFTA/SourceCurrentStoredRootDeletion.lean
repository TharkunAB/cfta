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
  | .node .. | .mu .. => denote value assignment
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

mutual
/-- Only original free names can affect deletion tests or assigned profiles. -/
theorem congr (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value)
    (firstCuts secondCuts : Reference → Bool) (first second : Reference → Profile)
    (cutAgree : ∀ name ∈ value.free, firstCuts name = secondCuts name)
    (agree : ∀ name ∈ value.free, first name = second name) :
    deleted firstCuts value first = deleted secondCuts value second := by
  cases value with
  | empty => rw [deleted,deleted]
  | reference name =>
      rw [deleted,deleted,cutAgree name List.mem_cons_self,agree name List.mem_cons_self]
  | node | mu =>
      rw [deleted,deleted]
      exact SourceCurrentStoredProfileFunction.congr _ state coherent available first second agree
  | union entry members depth free =>
      rw [deleted,deleted]
      apply congr_many members state coherent (fun child member => available.children child member)
      · intro child member name named
        apply cutAgree name
        rw [InternedNormalizationFree.union_free state coherent entry members depth free available.resident]
        exact (childFree_member members name).mpr ⟨child,member,named⟩
      · intro child member name named
        apply agree name
        rw [InternedNormalizationFree.union_free state coherent entry members depth free available.resident]
        exact (childFree_member members name).mpr ⟨child,member,named⟩
termination_by sizeOf value

/-- Ordered alternatives use only deletion tests and profiles on their own free names. -/
theorem congr_many (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Values state values)
    (firstCuts secondCuts : Reference → Bool) (first second : Reference → Profile)
    (cutAgree : ∀ value ∈ values, ∀ name ∈ value.free, firstCuts name = secondCuts name)
    (agree : ∀ value ∈ values, ∀ name ∈ value.free, first name = second name) :
    deletedMany firstCuts values first = deletedMany secondCuts values second := by
  cases values with
  | nil => rw [deletedMany,deletedMany]
  | cons head tail =>
      rw [deletedMany,deletedMany,
        congr head state coherent (available head List.mem_cons_self) firstCuts secondCuts first second
          (cutAgree head List.mem_cons_self) (agree head List.mem_cons_self),
        congr_many tail state coherent (fun child member => available child (List.mem_cons_of_mem _ member))
          firstCuts secondCuts first second
          (fun child member => cutAgree child (List.mem_cons_of_mem _ member))
          (fun child member => agree child (List.mem_cons_of_mem _ member))]
termination_by sizeOf values
end

/-- Deleting no original free name leaves the full assigned profile unchanged. -/
theorem absent (cuts : Reference → Bool) (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value)
    (missing : ∀ name ∈ value.free, cuts name = false) :
    deleted cuts value assignment = denote value assignment := by
  rw [congr value state normal.facts.coherent available cuts (fun _ => false) assignment assignment missing
    (fun _ _ => rfl)]
  exact uncut value assignment state normal available

end MicroCFTA.SourceCurrentStoredRootDeletion
