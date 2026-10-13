import MicroCFTA.MergedColdReaderFacts
import MicroCFTA.MergedPhysicalComparisonExample

/-!
# Actual cold edge-reader branches

The examples execute the ordinary Mu fast path, the visited-identity cycle
cutoff, and the explicit unresolved-union-reference error.
-/
namespace MicroCFTA.MergedSourceExposureExample
open InternedConstructorTemplates InternedNestedConstruction MergedSourceExposure

/-- The first natural-number exposure allocates its ordinary result and retains the recursive child. -/
theorem ordinary_fast_path :
    (match MergedSourceExposure.nodeEdges 0 MergedPhysicalComparisonExample.root MergedPhysicalComparisonExample.initial with
    | .done edges state => some (edges.map (fun edge => edge.entry.key.symbol), edges.map (fun edge => edge.children.map Value.referenceOf), state.nodes.next)
    | _ => none) = some ([0, 1], [[], [.mu 2]], 5) := by cbv

/-- A raw bare-self binder retains a physical recursive cycle. -/
def cycleBuilt := build (.binder false (.var 0) : Syntax Nat Unit) [] empty

/-- Retain the actual raw binder returned by source construction. -/
def cycleRoot : Value Nat Unit := match cycleBuilt with | .done value _ => value | .pending .. => .empty

/-- The recursive closure has no outgoing edge and terminates at its visited canonical identity. -/
theorem cycle_reader : MergedSourceExposure.nodeEdges 2 cycleRoot cycleBuilt.state = .done [] cycleBuilt.state := by cbv

/-- One worklist step is insufficient for the same cycle; the successful bound is substantive. -/
theorem cycle_short_fuel : MergedSourceExposure.nodeEdges 1 cycleRoot cycleBuilt.state = .exhausted cycleBuilt.state := by cbv

/-- Two unresolved primitive operands form an actual retained source union. -/
def openUnion := run (makeUnion [.reference .depth, .reference (.uninterned 0)] : Work Nat Unit (Value Nat Unit)) empty

/-- Source closure reports the first unresolved union reference instead of treating it as empty. -/
theorem unresolved_union : MergedSourceExposure.nodeEdges 2 openUnion.1 openUnion.2 = .unresolved .depth openUnion.2 := by cbv

/-- A direct reference follows the distinct source top-level empty-edge branch. -/
theorem direct_reference : MergedSourceExposure.nodeEdges 0 (.reference .depth) (empty : State Nat Unit) = .done [] empty := rfl

end MicroCFTA.MergedSourceExposureExample
