import MicroCFTA.SourceCurrentAllocatedClassEditPlan

#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_valid
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_populated
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_allowed
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_disjoint
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_nonroot
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_not_leaf
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_children
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_safe
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_condition
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_valid
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_populated
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_allowed
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_disjoint
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_nonroot
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_not_leaf
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_children
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_safe
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlan.compiled_condition

namespace MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes
open Language InternedConstructorTemplates
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain SourceCurrentAllocatedClassEditPlan

-- Literal compiled leaves retain exactly the original natural token and its signed path.
theorem compiled_tokens (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (signed : List Int) (token : EqualityNormalize.Path) :
    (signed, token) ∈ leaves (compiled record) ↔ token ∈ record.paths ∧ signed = token.map Int.ofNat := by
  have represented := SourceEqualityEditCompiledPaths.build_leaves _ (compiled_disjoint record coherent)
  constructor
  · intro member
    obtain ⟨original, present, same⟩ := List.mem_map.mp (represented.mem_iff.mp member)
    cases same
    exact ⟨present, rfl⟩
  · rintro ⟨present, rfl⟩
    exact represented.mem_iff.mpr (List.mem_map.mpr ⟨token, present, rfl⟩)

-- One coherent active record derives every lower completion precondition from selected domains.
theorem selected_plan (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (values : List (Value Symbol Guard))
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ entries, compiled record = .editBelow entries ∧ ChildrenSafe entries 0 values ∧
      Valid (compiled record) ∧ Populated (compiled record) ∧
      SourceEqualitySharedEditEffects.Allowed record (compiled record) := by
  obtain ⟨entries, built⟩ := compiled_children record coherent active
  exact ⟨entries, built, compiled_safe record coherent values domains entries built,
    compiled_valid record, compiled_populated record, compiled_allowed record⟩

end MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes

#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes.compiled_tokens
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes.selected_plan
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes.compiled_tokens
#check @MicroCFTA.SourceCurrentAllocatedClassEditPlanProbes.selected_plan
