import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWords

/-!
# Numeric capacity at one actual native query entry

The two current constructor supplies bound every resident ordinary operand.
The predicate contains no execution, readiness, or result condition.
The word adapters use separate initial physical and structural facts.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain

/-- Current node and edge supplies fit the two actual native key layouts. -/
def Capacity (bits : Nat) (state : Checked (bits + 2)) : Prop :=
  state.native.machine.heap.nodes.next ≤ 2 ^ bits ∧
    state.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)

/-- Numeric entry capacity derives all word checks for resident finite ordinary node operands. -/
theorem node_words [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right) (capacity : Capacity bits before) :
    WordRanges (.code (SourceRecursiveIntersectionCode.requestNode emptyDomain left right)) before :=
  SourceCurrentAllocatedFiniteOrdinaryWords.node_of_domain bits before good capacity.1 capacity.2
    left right leftAvailable rightAvailable leftDomain rightDomain

/-- Numeric entry capacity derives all word checks for complete resident finite ordinary rows. -/
theorem edge_words [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : EdgeValue Symbol Guard)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftDomain : DEdge left) (rightDomain : DEdge right) (capacity : Capacity bits before) :
    WordRanges (.code (SourceRecursiveIntersectionCode.requestEdge emptyDomain left right)) before :=
  SourceCurrentAllocatedFiniteOrdinaryWords.edge_of_domain bits before good capacity.1 capacity.2
    left right leftResident rightResident leftDomain rightDomain

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity
