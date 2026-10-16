import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget

namespace MicroCFTA.NativeBudgetIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open SourceCurrentAllocatedFiniteOrdinaryNativeBudget
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial static headroom derives both all-word checks and capacity at every actual node prefix. -/
theorem node_initial_headroom (bits : Nat) (before : SourceEqualityNativeDemand.State (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node left)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node right)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget left right ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + nodeBudget left right ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges (.code (requestNode emptyDomain left right)) before ∧
      ∀ fuel next after, Steps fuel (.code (requestNode emptyDomain left right)) before next after →
        Capacity bits after := by
  have initial : Capacity bits before := ⟨by omega, by omega⟩
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryCapacity.node_words bits before good left right
      leftAvailable rightAvailable leftDomain rightDomain initial,
    fun fuel next after actual => node_prefix_capacity bits before good left right leftAvailable rightAvailable
      leftDomain rightDomain nodes edges fuel next after actual⟩

/-- Original edge headroom permits unequal arities and unrestricted guards at every actual prefix. -/
theorem edge_initial_headroom (bits : Nat) (before : SourceEqualityNativeDemand.State (bits + 2)) (good : Good before)
    (left right : EdgeValue Symbol Guard)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge left)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge right)
    (nodes : before.native.machine.heap.nodes.next + edgeBudget left right ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget left right ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges (.code (requestEdge emptyDomain left right)) before ∧
      ∀ fuel next after, Steps fuel (.code (requestEdge emptyDomain left right)) before next after →
        Capacity bits after := by
  have initial : Capacity bits before := ⟨by omega, by omega⟩
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryCapacity.edge_words bits before good left right
      leftResident rightResident leftDomain rightDomain initial,
    fun fuel next after actual => edge_prefix_capacity bits before good left right leftResident rightResident
      leftDomain rightDomain nodes edges fuel next after actual⟩

#print axioms node_initial_headroom
#check @node_initial_headroom
#print axioms edge_initial_headroom
#check @edge_initial_headroom
end MicroCFTA.NativeBudgetIndependentKernels
