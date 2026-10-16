import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySerialCallerResources

namespace SerialCallerResourceChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceEqualityRequiredWorkerComplete (StableRun)
open SourceCurrentAllocatedFiniteOrdinarySerialCallerResources
open MergedOrdinaryHeight (childrenHeight)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial headroom bounds both final supplies at the same two literal returns. -/
theorem serial_layout_capacity {rows arity : Nat} (bits : Nat)
    (paths : List (List Int)) (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (available : InternedNestedProvenance.Values before values)
    (profile : ChildrenShape rows arity values) (count depth bound : Nat)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodeHeadroom : before.nodes.next + nodeBudget rows arity count bound ≤ 2 ^ bits)
    (edgeHeadroom : before.edges.next + edgeBudget rows arity count bound ≤ 2 ^ (bits + 2)) :
    ∃ middle current result after requests,
      StableRun (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) middle current ∧
      SourceEqualityProjectionGraph.Forest path middle current result after ∧
      StableRun (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path middle current) result after ∧
      SourceEqualityRequiredCache.Keeps before after ∧
      SourceEqualityRequiredSemanticCache.SemanticReady after ∧ Available after result ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows rows count depth) arity result ∧
      SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace before after requests ∧
      after.nodes.next ≤ 2 ^ bits ∧ after.edges.next ≤ 2 ^ (bits + 2) := by
  obtain ⟨middle, current, result, after, earlier, later, firstStable, actual, lastStable,
    kept, lastSemantic, lastAvailable, lastProfile, _lastHeight, trace, _nodeRequests,
    _edgeRequests, nodeSupply, edgeSupply⟩ :=
    required_projection paths path values before semantic available profile count depth bound lengthBound pathBound heightBound
  exact ⟨middle, current, result, after, earlier ++ later, firstStable, actual, lastStable,
    kept, lastSemantic, lastAvailable, lastProfile, trace,
    Nat.le_trans nodeSupply nodeHeadroom, Nat.le_trans edgeSupply edgeHeadroom⟩

#print axioms nodeBudget
#check @nodeBudget
#print axioms edgeBudget
#check @edgeBudget
#print axioms required_projection
#check @required_projection
#print axioms serial_layout_capacity
#check @serial_layout_capacity
end SerialCallerResourceChecks
