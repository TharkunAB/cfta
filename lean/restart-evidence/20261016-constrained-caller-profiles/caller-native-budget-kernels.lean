import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySerialCallerResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProfileBudget

namespace CallerNativeBudgetIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceEqualityRequiredWorkerComplete (StableRun)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "P" => SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows
local notation "BNode" => SourceCurrentAllocatedFiniteOrdinarySerialCallerResources.nodeBudget
local notation "BEdge" => SourceCurrentAllocatedFiniteOrdinarySerialCallerResources.edgeBudget
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial stage and native headroom bounds the next generated query without a result-profile premise. -/
theorem generated_native_headroom (rows arity count depth bound bits : Nat)
    (paths : List (List Int)) (path : List Int) (values : List Node) (right : Node)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (rightAvailable : Available before right)
    (profile : ChildrenShape rows arity values) (rightProfile : NodeShape rows arity right)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) (rightHeight : height right ≤ bound)
    (nodes : before.nodes.next + BNode rows arity count bound + N (P rows count depth) arity bound ≤ 2 ^ bits)
    (edges : before.edges.next + BEdge rows arity count bound + N (P rows count depth) arity bound ≤ 2 ^ (bits + 2)) :
    ∃ middle current result after earlier later,
      StableRun (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) middle current ∧
      SourceEqualityProjectionGraph.Forest path middle current result after ∧ Trace before after (earlier ++ later) ∧
      Available after result ∧ Available after right ∧ NodeShape (P rows count depth) arity result ∧
      SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget result right ≤ N (P rows count depth) arity bound ∧
      after.nodes.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget result right ≤ 2 ^ bits ∧
      after.edges.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget result right ≤ 2 ^ (bits + 2) := by
  obtain ⟨middle, current, result, after, earlier, later, firstStable, actual, _lastStable, keeps, _afterSemantic,
    resultAvailable, resultProfile, resultHeight, trace, _requestsN, _requestsE, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySerialCallerResources.required_projection paths path values before semantic available profile
      count depth bound lengthBound pathBound heightBound
  have rowBound : rows ≤ P rows count depth := by
    apply Nat.le_trans (Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.projectRows_base rows)
      (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.projectRows_mono rows (Nat.zero_le depth)))
    simpa only [SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows, Nat.one_mul] using
      Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.projectRows rows depth) (Nat.le_max_left 1 count)
  have rightProfile' := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.mono right rightProfile rowBound (Nat.le_refl _)
  have native := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.node_budget_le result right resultProfile rightProfile'
    bound (Nat.max_le.mpr ⟨resultHeight, rightHeight⟩)
  exact ⟨middle, current, result, after, earlier, later, firstStable, actual, trace, resultAvailable,
    keeps.available right rightAvailable, resultProfile, native, by omega, by omega⟩

end CallerNativeBudgetIntegration

#print axioms CallerNativeBudgetIntegration.generated_native_headroom
#check @CallerNativeBudgetIntegration.generated_native_headroom
