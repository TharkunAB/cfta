import MicroCFTA.SourceCurrentStoredRootDeletion

/-!
# Singleton deletion and the actual root self filter

Normalized union members are flat. Singleton deletion therefore removes
exactly the original bare self members of a union. The actual filter keeps
a standalone bare self reference. The pure equation retains this exception.
-/
namespace MicroCFTA.SourceCurrentStoredRootDeletionFilter
open InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combine combineMany)
open InternedUnionNormalForm (Atomic)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredFilteredProfile (filtered)
open SourceCurrentStoredRootDeletion (deleted deletedMany)
open SourceEqualityRequiredCache (Ready)

private theorem atomic (own : Reference) (value : Value Symbol Guard)
    (assignment : Reference → Profile) (flat : Atomic value) :
    deleted (fun name => name == own) value assignment =
      if value.referenceOf == .ref own then some [] else denote value assignment := by
  cases value with
  | empty => simpa only [deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false] using (SourceCurrentStoredProfileFunction.empty assignment).symm
  | reference name =>
      by_cases same : name = own
      · subst name
        simp [deleted,Value.referenceOf,beq_iff_eq]
      · simp [deleted,Value.referenceOf,beq_iff_eq,same,SourceCurrentStoredProfileFunction.reference]
  | node | mu => simp only [deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false]
  | union => cases flat

private theorem members (own : Reference) (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) (flat : ∀ value ∈ values, Atomic value) :
    deletedMany (fun name => name == own) values assignment = combineMany
      ((values.filter (fun value => value.referenceOf != .ref own)).map (fun value => denote value assignment)) := by
  cases values with
  | nil => rw [deletedMany]; rfl
  | cons first rest =>
      rw [deletedMany,atomic own first assignment (flat first List.mem_cons_self),
        members own rest assignment (fun value member => flat value (List.mem_cons_of_mem _ member))]
      by_cases cut : first.referenceOf == .ref own
      · simp only [cut,ite_true,List.filter_cons,bne,Bool.not_true,Bool.false_eq_true,ite_false]
        generalize combineMany ((rest.filter (fun value => !(value.referenceOf == .ref own))).map (fun value => denote value assignment)) = current
        cases current <;> rfl
      · have kept : (first.referenceOf == .ref own) = false := Bool.eq_false_iff.mpr cut
        simp only [kept,Bool.false_eq_true,ite_false,List.filter_cons,bne,Bool.not_false,ite_true,List.map_cons,combineMany]

/-- Singleton deletion agrees with filtering except at a standalone bare self reference. -/
theorem singleton (own : Reference) (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    filtered own value assignment =
      if value.referenceOf == .ref own then assignment own
      else deleted (fun name => name == own) value assignment := by
  cases value with
  | empty =>
      simpa only [filtered,deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false] using SourceCurrentStoredProfileFunction.empty assignment
  | reference name =>
      by_cases same : name = own
      · subst name
        simp [filtered,Value.referenceOf,beq_iff_eq,SourceCurrentStoredProfileFunction.reference]
      · simp [filtered,deleted,Value.referenceOf,beq_iff_eq,same,SourceCurrentStoredProfileFunction.reference]
  | node | mu => simp only [filtered,deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false]
  | union entry values depth free =>
      have flat := InternedUnionNormalForm.resident_flat state normal.flat _ available.resident
      simpa only [filtered,deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false] using (members own values assignment flat).symm

/-- Actual ready filtering supplies the singleton deletion profile with the same bare exception. -/
theorem filter_profile [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state value) :
    Equivalent (denote (run (withoutSelfReference own value) state).1 assignment)
      (if value.referenceOf == .ref own then assignment own
        else deleted (fun name => name == own) value assignment) := by
  rw [← singleton own value assignment state ready.semantic.1.normal available]
  exact SourceCurrentStoredFilteredProfile.filter_profile own value assignment state ready available

end MicroCFTA.SourceCurrentStoredRootDeletionFilter
