import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources
import MicroCFTA.SourceEqualityClassTarget

/-!
# Uniform bounds for the original class targets

A selected member removes one distinct path from its class.
The whole Target bounds use the resulting full operand count.
No execution or returned profile is an input to the numeric bounds.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds
open EqualityNormalize
open SourceEqualityClassOrder (Record Coherent)
open SourceEqualityClassTarget (operandPaths)
namespace Target
export SourceCurrentAllocatedFiniteOrdinaryTargetResources (outputRows nodeBudget edgeBudget)
end Target
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers (targetRows_mono node_mono edge_mono)
end Numbers

/-- More full operand paths permit every earlier whole-Target row bound. -/
theorem target_rows_mono (rows count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    Target.outputRows rows count depth bound first ≤ Target.outputRows rows count depth bound last := by
  cases first with
  | zero => exact Nat.zero_le _
  | succ first =>
      cases last with
      | zero => omega
      | succ last => exact Numbers.targetRows_mono rows count depth bound (by omega)

/-- More full operand paths permit every earlier whole-Target node budget. -/
theorem target_nodes_mono (rows arity count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    Target.nodeBudget rows arity count depth bound first ≤ Target.nodeBudget rows arity count depth bound last := by
  cases first with
  | zero => exact Nat.zero_le _
  | succ first =>
      cases last with
      | zero => omega
      | succ last => exact Numbers.node_mono rows arity count depth bound (by omega)

/-- More full operand paths permit every earlier whole-Target edge budget. -/
theorem target_edges_mono (rows arity count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    Target.edgeBudget rows arity count depth bound first ≤ Target.edgeBudget rows arity count depth bound last := by
  cases first with
  | zero => exact Nat.zero_le _
  | succ first =>
      cases last with
      | zero => omega
      | succ last => exact Numbers.edge_mono rows arity count depth bound (by omega)

/-- Removing a member of a distinct class removes exactly one operand. -/
theorem operand_paths_length (paths : Class) (selected : Path) (distinct : paths.Nodup) (member : selected ∈ paths) :
    (operandPaths paths selected).length = paths.length - 1 := by
  have filtered : paths.filter (fun path => decide (path ≠ selected)) = paths.filter (· != selected) := by
    apply List.filter_congr
    intro path _
    by_cases same : path = selected <;> simp [same]
  have erased := List.length_erase_of_mem member
  rw [distinct.erase_eq_filter selected] at erased
  simpa only [operandPaths, List.length_map, EqualityNarrowing.others, filtered] using erased

/-- Coherent source records derive the exact selected operand count. -/
theorem record_operand_paths_length (record : Record) (coherent : Coherent record) (selected : Path)
    (member : selected ∈ record.paths) :
    (operandPaths record.paths selected).length = record.paths.length - 1 :=
  operand_paths_length record.paths selected (coherent.2.1 ▸ canonicalClass_nodup record.paths) member

/-- Signed path conversion and selected-path removal retain the original depth bound. -/
theorem operand_paths_depth (paths : Class) (selected : Path) (depth : Nat)
    (bounded : ∀ path ∈ paths, path.length ≤ depth) :
    ∀ path ∈ operandPaths paths selected, path.length ≤ depth := by
  intro path member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  simpa only [List.length_map] using bounded original (List.mem_filter.mp included).1

/-- One original record bound controls every selected target count and depth. -/
theorem record_target_bounds (record : Record) (coherent : Coherent record) (selected : Path)
    (member : selected ∈ record.paths) (rows arity count depth bound members : Nat)
    (lengthBound : record.paths.length ≤ members) (depthBound : ∀ path ∈ record.paths, path.length ≤ depth) :
    Target.outputRows rows count depth bound (operandPaths record.paths selected).length ≤
        Target.outputRows rows count depth bound (members - 1) ∧
    Target.nodeBudget rows arity count depth bound (operandPaths record.paths selected).length ≤
        Target.nodeBudget rows arity count depth bound (members - 1) ∧
    Target.edgeBudget rows arity count depth bound (operandPaths record.paths selected).length ≤
        Target.edgeBudget rows arity count depth bound (members - 1) ∧
    (∀ path ∈ operandPaths record.paths selected, path.length ≤ depth) := by
  have counted := record_operand_paths_length record coherent selected member
  have enough : (operandPaths record.paths selected).length ≤ members - 1 := by omega
  exact ⟨target_rows_mono rows count depth bound enough,
    target_nodes_mono rows arity count depth bound enough,
    target_edges_mono rows arity count depth bound enough,
    operand_paths_depth record.paths selected depth depthBound⟩

/-- A derived target profile fits the common bound for every selected class member. -/
theorem record_profile (record : Record) (coherent : Coherent record) (selected : Path)
    (member : selected ∈ record.paths) (rows arity count depth bound members : Nat)
    (lengthBound : record.paths.length ≤ members)
    (value : InternedConstructorTemplates.Value Symbol Guard)
    (profile : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
      (Target.outputRows rows count depth bound (operandPaths record.paths selected).length) arity value) :
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
      (Target.outputRows rows count depth bound (members - 1)) arity value := by
  have counted := record_operand_paths_length record coherent selected member
  exact SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.mono value profile
    (target_rows_mono rows count depth bound (by omega)) (Nat.le_refl arity)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds
