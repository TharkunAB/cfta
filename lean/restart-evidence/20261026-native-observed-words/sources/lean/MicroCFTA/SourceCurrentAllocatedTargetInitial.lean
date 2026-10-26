import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

/-!
# Current target queries from initial numeric room

Initial counters and domain room derive the reached word checks.
The existing query producer returns the full receipt at its actual endpoint.
A supplied raw return is verified only under the same initial premises.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial numeric room constructs the full target receipt with the same warm tables. -/
theorem finite_initial (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Value Symbol Guard) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next : Inventory, ∃ value after,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before value after memos := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original
    left before.native.machine.heap ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original
    right before.native.machine.heap ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges
    bits before ready.good ready.semantic left right leftOriginal rightOriginal
      leftAvailable rightAvailable nodes edges room
  exact finite formulas solver inventory left right before ready admitted
    leftAvailable rightAvailable leftClosed rightClosed ranges.1 memos valid

/-- The same initial premises verify a raw return at its literal value and full state. -/
theorem raw_done_verified_initial (bits givenFuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right value : Value Symbol Guard) (before after : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (done : execute givenFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
      .done value after) :
    ∃ next : Inventory,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before value after memos := by
  obtain ⟨next, result, reached, source, roots, receipt⟩ := finite_initial bits formulas solver inventory
    left right before ready admitted leftAvailable rightAvailable leftClosed rightClosed nodes edges room memos valid
  obtain ⟨fuel, actual⟩ := receipt.actual.done
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique
    givenFuel fuel _ before after reached value result done actual
  exact ⟨next, source, roots, receipt⟩

end MicroCFTA.SourceCurrentAllocatedTargetQuery
