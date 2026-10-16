import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCallerResources

namespace CallerResourceIndependentChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Counts" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A constructed Required return supplies every physical and profile input of the next Projection. -/
theorem required_then_projection {rows arity : Nat} (paths : List (List Int)) (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rows arity values)
    (count depth bound : Nat) (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    ∃ middleValues middle result after requests,
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) middleValues middle ∧
      SourceEqualityProjectionGraph.Forest path middleValues middle result after ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path middleValues middle) result after ∧
      Keeps before after ∧ SemanticReady after ∧ Available after result ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows rows count depth) arity result ∧
      height result ≤ bound ∧ Trace before after requests ∧
      nodeRequests requests ≤ (Counts values).1 + (1 + (Counts middleValues).1) ∧
      edgeRequests requests ≤ (Counts values).2 := by
  obtain ⟨middleValues, middle, one, firstStable, firstKept, middleSemantic, middleAvailable, middleProfile,
      middleHeight, middleLength, oneTrace, oneNodes, oneEdges, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.required paths values before semantic available profile
  obtain ⟨result, after, two, actual, projectionStable, lastKept, afterSemantic, resultAvailable, resultProfile,
      resultHeight, twoTrace, twoNodes, twoEdges, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.projection path middleValues middle middleSemantic middleAvailable middleProfile
      count depth bound (by simpa only [middleLength] using lengthBound) pathBound (Nat.le_trans middleHeight heightBound)
  refine ⟨middleValues, middle, result, after, one ++ two, firstStable, actual, projectionStable, firstKept.trans lastKept,
    afterSemantic, resultAvailable, resultProfile, resultHeight, .trans oneTrace twoTrace, ?_, ?_⟩
  · rw [nodeRequests_append]; omega
  · rw [edgeRequests_append]; omega

#print axioms required_then_projection
#check @required_then_projection
end CallerResourceIndependentChecks
