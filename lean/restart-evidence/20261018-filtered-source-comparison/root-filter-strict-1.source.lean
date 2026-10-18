import MicroCFTA.SourceCurrentStoredProfileComposition

/-!
# Assigned profiles after original root self filtering

The filter tests original bare references before substitution. It removes
the selected reference from a root union. It retains a standalone reference.
The function below keeps that distinction before it assigns profiles.
-/
namespace MicroCFTA.SourceCurrentStoredFilteredProfile
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combineMany)
open InternedBinderProtocol (Reference)
open SourceCurrentStoredProfileFunction (denote)
open SourceEqualityRequiredCache (Ready)

/-- Filter original root union members before assigning their profiles. -/
def filtered (own : Reference) (value : Value Symbol Guard) (assignment : Reference → Profile) : Profile :=
  match value with
  | .union _ members _ _ => combineMany
      ((members.filter (fun member => member.referenceOf != .ref own)).map (fun member => denote member assignment))
  | _ => denote value assignment

/-- A standalone reference remains present, including the selected self reference. -/
theorem reference (own name : Reference) (assignment : Reference → Profile) :
    filtered own (.reference name : Value Symbol Guard) assignment = assignment name :=
  SourceCurrentStoredProfileFunction.reference name assignment

/-- A root Mu remains literal for the original root filter. -/
theorem mu (own : Reference) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (assignment : Reference → Profile) :
    filtered own (.mu entry body depth ordinary) assignment = denote (.mu entry body depth ordinary) assignment := rfl

/-- Actual filtering gives the assigned profile of the retained original members. -/
theorem filter_profile [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state value) :
    Equivalent (denote (run (withoutSelfReference own value) state).1 assignment)
      (filtered own value assignment) := by
  cases value with
  | empty | reference name | node entry edges depth free | mu entry body depth ordinary =>
      simp only [withoutSelfReference,run,filtered]
      exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
  | union entry members depth free =>
      by_cases present : members.any (fun member => member.referenceOf == .ref own) = true
      · simp only [withoutSelfReference,present,ite_true,filtered]
        apply SourceCurrentStoredProfileComposition.makeUnion _ assignment state ready
        intro member included
        exact available.children member (List.mem_filter.mp included).1
      · have unchanged : members.filter (fun member => member.referenceOf != .ref own) = members := by
          apply List.filter_eq_self.mpr
          intro member included
          apply Bool.not_eq_true.mpr
          intro selected
          exact present (List.any_eq_true.mpr ⟨member,included,selected⟩)
        simp only [withoutSelfReference,present,ite_false,run,filtered,unchanged]
        rw [SourceCurrentStoredProfileComposition.union entry members depth free assignment state
          ready.semantic.1.normal available]
        exact ⟨Iff.rfl,fun _ => Iff.rfl⟩

end MicroCFTA.SourceCurrentStoredFilteredProfile
