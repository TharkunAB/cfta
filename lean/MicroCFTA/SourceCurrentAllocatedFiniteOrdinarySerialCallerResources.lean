import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCallerResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds

/-!
# Initial-only reservations for Required followed by Projection

Initial row, arity, height, and forest-size limits bound both stages.
The first actual return derives the second stage's input facts.
No intermediate occurrence count, result profile, or completion is supplied.
The result concerns the two constructor supplies, not host counters.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySerialCallerResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceEqualityRequiredWorkerComplete (StableRun)
open MergedOrdinaryHeight (height childrenHeight)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Reserve both node stages from the original forest profile. -/
def nodeBudget (rows arity count bound : Nat) : Nat :=
  2 * (count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound) + 1

/-- Required can rebuild each original edge; Projection adds no edge request. -/
def edgeBudget (rows arity count bound : Nat) : Nat :=
  count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount rows arity bound

/-- Initial profiles construct both actual returns with one cumulative reservation. -/
theorem required_projection {rows arity : Nat} (paths : List (List Int)) (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (profile : ChildrenShape rows arity values)
    (count depth bound : Nat) (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    ∃ middle current result after earlier later,
      StableRun (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) middle current ∧
      SourceEqualityProjectionGraph.Forest path middle current result after ∧
      StableRun (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path middle current) result after ∧
      Keeps before after ∧ SemanticReady after ∧ Available after result ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows rows count depth) arity result ∧
      height result ≤ bound ∧ Trace before after (earlier ++ later) ∧
      nodeRequests (earlier ++ later) ≤ nodeBudget rows arity count bound ∧
      edgeRequests (earlier ++ later) ≤ edgeBudget rows arity count bound ∧
      after.nodes.next ≤ before.nodes.next + nodeBudget rows arity count bound ∧
      after.edges.next ≤ before.edges.next + edgeBudget rows arity count bound := by
  obtain ⟨middle, current, earlier, firstStable, firstKeeps, firstSemantic, firstAvailable,
    firstProfile, firstHeight, firstLength, firstTrace, firstNodes, firstEdges, firstNodeSupply, firstEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.required paths values before semantic available profile
  have middleHeight : childrenHeight middle ≤ bound := Nat.le_trans firstHeight heightBound
  have middleLength : middle.length ≤ count := Nat.le_trans (Nat.le_of_eq firstLength) lengthBound
  obtain ⟨result, after, later, actual, lastStable, lastKeeps, lastSemantic, lastAvailable, lastProfile,
    lastHeight, lastTrace, lastNodes, lastEdges, lastNodeSupply, lastEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.projection path middle current firstSemantic firstAvailable firstProfile
      count depth bound middleLength pathBound middleHeight
  have initialCounts := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
  have middleCounts := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children middle firstProfile bound middleHeight
  have initialNodeBound := Nat.le_trans initialCounts.1
    (Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound) lengthBound)
  have middleNodeBound := Nat.le_trans middleCounts.1
    (Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound) middleLength)
  have initialEdgeBound := Nat.le_trans initialCounts.2
    (Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount rows arity bound) lengthBound)
  refine ⟨middle, current, result, after, earlier, later, firstStable, actual, lastStable, firstKeeps.trans lastKeeps,
    lastSemantic, lastAvailable, lastProfile, lastHeight, .trans firstTrace lastTrace, ?_, ?_, ?_, ?_⟩
  · rw [nodeRequests_append]
    unfold nodeBudget
    omega
  · rw [edgeRequests_append, lastEdges]
    unfold edgeBudget
    omega
  · unfold nodeBudget
    omega
  · unfold edgeBudget
    omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySerialCallerResources
