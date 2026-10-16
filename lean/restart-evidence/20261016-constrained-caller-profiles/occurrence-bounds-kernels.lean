import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile

namespace OccurrenceBoundChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds
open MergedOrdinaryHeight (height childrenHeight)

def lower : Value Nat Nat := .node ⟨1, .node [2, 3]⟩
  [.mk ⟨2, ⟨0, [], 0⟩⟩ [], .mk ⟨3, ⟨0, [], 1⟩⟩ []] 0 []

def repeatedTree : Value Nat Nat := .node ⟨6, .node [4, 5]⟩
  [.mk ⟨4, ⟨1, [.node 1, .node 1, .node 1], 0⟩⟩ [lower, lower, lower],
    .mk ⟨5, ⟨1, [.node 1, .node 1, .node 1], 1⟩⟩ [lower, lower, lower]] 0 []

/-- The pure bound counts repeated physical child identities as distinct source occurrences. -/
theorem saturated_repeated_tree :
    NodeShape 2 3 repeatedTree ∧ height repeatedTree = 2 ∧
      SourceCurrentAllocatedFiniteOrdinaryOccurrences.node repeatedTree = (7, 14) ∧
      nodeCount 2 3 2 = 7 ∧ edgeCount 2 3 2 = 14 := by
  simp [NodeShape, RowsShape, EdgeShape, ChildrenShape, repeatedTree, lower, height,
    MergedOrdinaryHeight.edgesHeight, MergedOrdinaryHeight.edgeHeight, childrenHeight,
    SourceCurrentAllocatedFiniteOrdinaryOccurrences.node, SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows,
    SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge, SourceCurrentAllocatedFiniteOrdinaryOccurrences.children,
    nodeCount, edgeCount]

/-- The general theorem bounds this repeated tree from its initial profile and height only. -/
theorem repeated_tree_bound :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.node repeatedTree).1 ≤ 7 ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.node repeatedTree).2 ≤ 14 := by
  simpa only [nodeCount, edgeCount] using node repeatedTree saturated_repeated_tree.1 2
    (Nat.le_of_eq saturated_repeated_tree.2.1)

variable {Symbol Guard : Type} {rows arity : Nat} [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem narrow_height {values results : List (Value Symbol Guard)}
    (related : Language.All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results) :
    childrenHeight results ≤ childrenHeight values := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans first.2 (Nat.le_max_left _ _),
        Nat.le_trans ih (Nat.le_max_right _ _)⟩

/-- A Required result gets an input-only occurrence bound from its preserved profile, length, and height. -/
theorem required_result_bound (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (available : InternedNestedProvenance.Values before values)
    (profile : ChildrenShape rows arity values) (count bound : Nat)
    (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children results).1 ≤ count * nodeCount rows arity bound ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children results).2 ≤ count * edgeCount rows arity bound := by
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.requireAll_done fuel readFuel paths values results before after
    done semantic available profile
  have structural := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel paths values results before after
    done semantic available (ChildrenShape.domain values profile)
  have narrower := narrow_height structural.2.2.2.2
  have counted := children results physical.2.2.2.1 bound (Nat.le_trans narrower heightBound)
  have finalLength : results.length ≤ count := by simpa only [physical.2.2.2.2] using lengthBound
  exact ⟨Nat.le_trans counted.1 (Nat.mul_le_mul_right _ finalLength),
    Nat.le_trans counted.2 (Nat.mul_le_mul_right _ finalLength)⟩

#print axioms saturated_repeated_tree
#check @saturated_repeated_tree
#print axioms repeated_tree_bound
#check @repeated_tree_bound
#print axioms required_result_bound
#check @required_result_bound
end OccurrenceBoundChecks
