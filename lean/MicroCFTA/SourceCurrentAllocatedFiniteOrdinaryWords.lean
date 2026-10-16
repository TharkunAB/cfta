import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordExecution
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Initial word bounds for finite ordinary native queries

Every actual recursive request uses an original input record.
The initial recursive key bounds therefore suffice for all yielded prefixes.
Only the initial node and edge supplies occur in the counter-bound adapter.
There is no bound on generated results or later constructor supplies.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWords
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "KNode" => SourceCurrentAllocatedFiniteOrdinaryKeys.Node
local notation "KEdge" => SourceCurrentAllocatedFiniteOrdinaryKeys.Edge
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial physical validity and recursive original keys derive every reached node-query word check. -/
theorem node (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right) :
    WordRanges (.code (requestNode emptyDomain left right)) before := by
  apply SourceCurrentAllocatedFiniteOrdinaryWordExecution.word_ranges bits before.native.machine good.native.machine
    (.code (requestNode emptyDomain left right)) before
    (SourceCurrentAllocatedFiniteOrdinaryWordExecution.Origins.of_valid before.native good.native)
  exact SourceCurrentAllocatedFiniteOrdinaryWordCode.request_node bits before.native.machine
    ⟨emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩

/-- Only initial constructor supplies need bounds; all descendant word checks follow internally. -/
theorem node_of_domain (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right) :
    WordRanges (.code (requestNode emptyDomain left right)) before := by
  exact node bits before good left right leftAvailable rightAvailable
    (SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
      good.native.machine.1.coherent good.native.machine.1.linked nodes edges left leftAvailable leftDomain)
    (SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
      good.native.machine.1.coherent good.native.machine.1.linked nodes edges right rightAvailable rightDomain)

/-- Resident original rows derive word safety through the actual checked allocation and child schedule. -/
theorem edge (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : EdgeValue Symbol Guard)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftKeys : KEdge bits left) (rightKeys : KEdge bits right) :
    WordRanges (.code (requestEdge emptyDomain left right)) before := by
  apply SourceCurrentAllocatedFiniteOrdinaryWordExecution.word_ranges bits before.native.machine good.native.machine
    (.code (requestEdge emptyDomain left right)) before
    (SourceCurrentAllocatedFiniteOrdinaryWordExecution.Origins.of_valid before.native good.native)
  exact SourceCurrentAllocatedFiniteOrdinaryWordCode.request_edge bits before.native.machine
    ⟨emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftResident, rightResident⟩

/-- Initial row and node supplies suffice for every raw row and tagged descendant request. -/
theorem edge_of_domain (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (left right : EdgeValue Symbol Guard)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftDomain : DEdge left) (rightDomain : DEdge right) :
    WordRanges (.code (requestEdge emptyDomain left right)) before := by
  exact edge bits before good left right leftResident rightResident
    (SourceCurrentAllocatedFiniteOrdinaryKeys.of_resident bits before.native.machine.heap
      good.native.machine.1 nodes edges left leftResident leftDomain)
    (SourceCurrentAllocatedFiniteOrdinaryKeys.of_resident bits before.native.machine.heap
      good.native.machine.1 nodes edges right rightResident rightDomain)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWords
