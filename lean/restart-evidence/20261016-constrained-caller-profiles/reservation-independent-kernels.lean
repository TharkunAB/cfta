import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionReservations

namespace MicroCFTA.ProjectionReservationIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height childrenHeight)
local notation "O" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.node
local notation "OChildren" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children

private def leaf : Value Nat Nat := .node ⟨1, .node []⟩ [] 77 []
private def row : EdgeValue Nat Nat := .mk ⟨2, ⟨3, [.node 1, .node 1], 91⟩⟩ [leaf, leaf]
private def root : Value Nat Nat := .node ⟨3, .node [2, 2]⟩ [row, row] 88 []

/-- Static occurrence counts retain duplicated rows and child positions. -/
theorem repeated_original_occurrences : O root = (5, 2) ∧ OChildren [root, root] = (10, 4) := by
  exact ⟨rfl, rfl⟩

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm node still records one request even when its whole returned heap and supply stay fixed. -/
theorem warm_request_without_reservation (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before) (retained : canonicalEdges (surviving edges) ≠ []) :
    let warm := (run (makeNode edges) before).2
    ∃ requests, Trace warm warm requests ∧ nodeRequests requests = 1 ∧
      nodeReservations requests = 0 ∧ edgeRequests requests = 0 := by
  dsimp only
  let warm := (run (makeNode edges) before).2
  have repeated := replay (makeNode edges) before warm valid (grows_refl _)
  have actual : Trace warm warm (observe (makeNode edges) warm) := by
    simpa only [repeated] using Trace.work warm (makeNode edges)
  have counts := makeNode_requests edges warm
  have exactCounts := actual.next_exact
  exact ⟨observe (makeNode edges) warm, actual, by simpa [retained] using counts.1,
    by omega, counts.2⟩

/-- Profile, height, actual Work, and both supply facts refer to one supplied forest return. -/
theorem same_forest_profile_and_work {rows arity : Nat} {path : List Int}
    {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (profile : ChildrenShape rows arity values) :
    ∃ requests, Trace before after requests ∧
      nodeRequests requests ≤ 1 + (OChildren values).1 ∧ edgeRequests requests = 0 ∧
      after.nodes.next ≤ before.nodes.next + (1 + (OChildren values).1) ∧ after.edges.next = before.edges.next ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows rows values.length path.length) arity result ∧
      height result ≤ childrenHeight values := by
  have shaped := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forest actual semantic available profile
    values.length (childrenHeight values) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨requests, trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.forest actual semantic available (ChildrenShape.domain values profile)
  exact ⟨requests, trace, nodes, edges, nodeSupply, edgeSupply, shaped⟩

/-- Two supplied projections retain actual request order and derive the second entry facts from the first return. -/
theorem serial_actual_work {firstPath secondPath : List Int} {input middle result : Value Symbol Guard}
    {before current after : State Symbol Guard}
    (first : Project firstPath input before middle current) (second : Project secondPath middle current result after)
    (semantic : SemanticReady before) (available : Available before input)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node input) :
    ∃ earlier later, Trace before current earlier ∧ Trace current after later ∧ Trace before after (earlier ++ later) ∧
      nodeRequests (earlier ++ later) ≤ (O input).1 + (O middle).1 ∧ edgeRequests (earlier ++ later) = 0 ∧
      after.edges.next = before.edges.next := by
  obtain ⟨earlier, firstTrace, firstNodes, firstEdges, _, firstSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.project first semantic available domain
  have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.project first semantic available domain
  obtain ⟨later, secondTrace, secondNodes, secondEdges, _, secondSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.project second physical.2.1 physical.2.2.1 physical.2.2.2
  exact ⟨earlier, later, firstTrace, secondTrace, .trans firstTrace secondTrace,
    by rw [nodeRequests_append]; omega, by rw [edgeRequests_append, firstEdges, secondEdges], secondSupply.trans firstSupply⟩

#print axioms repeated_original_occurrences
#check @repeated_original_occurrences
#print axioms warm_request_without_reservation
#check @warm_request_without_reservation
#print axioms same_forest_profile_and_work
#check @same_forest_profile_and_work
#print axioms serial_actual_work
#check @serial_actual_work
end MicroCFTA.ProjectionReservationIndependentKernels
