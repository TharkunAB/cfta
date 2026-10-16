import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionReservations
import MicroCFTA.SourceEqualityProjectionComplete
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Constructed Required and Projection returns with resource bounds

Initial resident profiles construct the actual finite return.
The same returned graph derives profiles, height, request logs, and supplies.
No completed graph, child callback, or returned profile is supplied.
Outer capacity and merge reservations remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCallerResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceEqualityRequiredWorkerComplete (StableRun)
open MergedOrdinaryHeight (height childrenHeight)
local notation "OChildren" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem narrow_height {values results : List (Value Symbol Guard)}
    (actual : All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results) :
    childrenHeight results ≤ childrenHeight values := by
  induction actual with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans first.2 (Nat.le_max_left _ _), Nat.le_trans ih (Nat.le_max_right _ _)⟩

/-- Initial profiles construct stable requireAll and its actual constructor reservation. -/
theorem required {rows arity : Nat} (paths : List (List Int)) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values)
    (profile : ChildrenShape rows arity values) :
    ∃ results after requests,
      StableRun (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) results after ∧
      Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenShape rows arity results ∧
      childrenHeight results ≤ childrenHeight values ∧ results.length = values.length ∧
      Trace before after requests ∧ nodeRequests requests ≤ (OChildren values).1 ∧ edgeRequests requests ≤ (OChildren values).2 ∧
      after.nodes.next ≤ before.nodes.next + (OChildren values).1 ∧ after.edges.next ≤ before.edges.next + (OChildren values).2 := by
  obtain ⟨results, after, keeps, afterSemantic, afterAvailable, resultProfile, length, stable⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.finite paths values before semantic available profile
  obtain ⟨fuel, readFuel, completed⟩ := stable
  have done := completed fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have domain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.domain values profile
  have structural := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel paths values results before after
    done semantic available domain
  obtain ⟨requests, trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRequiredReservations.requireAll_done fuel readFuel paths values results before after
      done semantic available domain
  exact ⟨results, after, requests, ⟨fuel, readFuel, completed⟩, keeps, afterSemantic, afterAvailable,
    resultProfile, narrow_height structural.2.2.2.2, length, trace, nodes, edges, nodeSupply, edgeSupply⟩

/-- Initial forest limits construct stable projection with the same result profile and Work log. -/
theorem projection {rows arity : Nat} (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values)
    (profile : ChildrenShape rows arity values) (count depth bound : Nat)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    ∃ result after requests,
      SourceEqualityProjectionGraph.Forest path values before result after ∧
      StableRun (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path values before) result after ∧
      Keeps before after ∧ SemanticReady after ∧ Available after result ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows rows count depth) arity result ∧
      height result ≤ bound ∧ Trace before after requests ∧ nodeRequests requests ≤ 1 + (OChildren values).1 ∧ edgeRequests requests = 0 ∧
      after.nodes.next ≤ before.nodes.next + (1 + (OChildren values).1) ∧ after.edges.next = before.edges.next := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.domain values profile
  have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before semantic.ready.semantic.1.normal.facts.coherent value
      (available value member) (domain.member value member)
  obtain ⟨result, after, actual, keeps, afterSemantic, resultAvailable, _free⟩ :=
    SourceEqualityProjectionComplete.forest_complete path values before semantic available closed
  have resultProfile := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forest_uniform actual semantic available profile
    count depth bound lengthBound pathBound heightBound
  obtain ⟨requests, trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.forest actual semantic available domain
  exact ⟨result, after, requests, actual, SourceEqualityProjectionWorkerComplete.forest_stable actual, keeps,
    afterSemantic, resultAvailable, resultProfile.1, resultProfile.2, trace, nodes, edges, nodeSupply, edgeSupply⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCallerResources
