import MicroCFTA.SourceCurrentAllocatedNativeRequestResults

/-!
# Existing residency at the actual completed edge query endpoint

The existing edge_result theorem uses the same protected physical trace.
The original supplied execution budget and done equation stay in the caller.
-/
namespace MicroCFTA.EdgeQueryEndpointResidencyApplication
open InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

example {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (fuel traceFuel : Nat) (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (_done : execute fuel (.code (requestEdge request.domain request.left request.right)) before =
      .done value after)
    (actual : Trace traceFuel (.code (requestEdge request.domain request.left request.right)) before
      (.code (.pure value)) after) :
    EdgeResident after.native.machine.heap value := by
  exact SourceCurrentAllocatedNativeRequestResults.edge_result
    traceFuel request before after value physical actual

end MicroCFTA.EdgeQueryEndpointResidencyApplication
