import MicroCFTA.SourceCurrentAllocatedRecursiveAllocationTrace

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000

namespace MicroCFTA.AllocationTraceIndependentIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedRecursiveAllocationTrace
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A used optional binder constructs its own return before the literal allocated-edge continuation. -/
theorem used_optional_work (pair : Nat × Nat) (body : Value Symbol Guard) (before : Checked width)
    (good : Good before) (available : Available before.native.machine.heap body)
    (used : InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free)
    (symbol : Symbol) (guard : Guard) (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations guard) :
    let start : Control (EdgeValue Symbol Guard) :=
      .code (.optionalBinder pair body (fun value => .work (makeEdge symbol guard [value]) .pure))
    ∃ value heap middle result after,
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap = .done value heap ∧
      InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free ∧
      middle.native.machine.heap = heap ∧
      step start before = .yielded (.code (.work (makeEdge symbol guard [value]) .pure)) middle ∧
      step (.code (.work (makeEdge symbol guard [value]) .pure)) middle = .yielded (.code (.pure result)) after ∧
      Trace 2 start before (.code (.pure result)) after ∧ Good after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget pair body ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget pair body + 1 ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ after.operations = before.operations := by
  let start : Control (EdgeValue Symbol Guard) :=
    .code (.optionalBinder pair body (fun value => .work (makeEdge symbol guard [value]) .pure))
  obtain ⟨value, heap, completed, _context, _depth, _covered, output, _growth, _history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body before.native.machine.heap
      good.heap.semantic.1 available good.heap.semantic.2 good.heap.covered
  let middle : Checked width :=
    ⟨advance before.native {before.native.machine with heap := heap}, before.operations⟩
  let edgeWork := run (makeEdge symbol guard [value]) heap
  let after : Checked width :=
    ⟨advance middle.native {middle.native.machine with heap := edgeWork.2}, middle.operations⟩
  have first : step start before = .yielded (.code (.work (makeEdge symbol guard [value]) .pure)) middle := by
    simp only [start, step, SourceRecursiveIntersectionNative.step, completed, lift, middle]
  have second : step (.code (.work (makeEdge symbol guard [value]) .pure)) middle =
      .yielded (.code (.pure edgeWork.1)) after := rfl
  have input : SourceCurrentAllocatedNativePhysicalExecution.Inputs start before := available
  have later : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (.work (makeEdge symbol guard [value]) .pure)) middle :=
    SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge symbol guard [value] (by
      intro child member
      cases List.mem_singleton.mp member
      exact output)
  have actual : Trace 2 start before (.code (.pure edgeWork.1)) after :=
    .cons _ _ _ _ _ _ 1 input first (.cons _ _ _ _ _ _ 0 later second (.refl _ _))
  have fields : Fields start before := by
    intro result
    exact ⟨SourceCurrentAllocatedNativeCodeFields.makeEdge_fields before.operations symbol guard [result] field,
      fun _ => trivial⟩
  have bounded := prefix_bound actual good fields
  have charges : chargesThrough 2 start before = (SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget pair body, SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget pair body + 1) := by
    simp only [chargesThrough, first, second, stepCharges, start,
      SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe,
      SourceCurrentAllocatedFiniteOrdinaryReservations.nodeRequests,
      SourceCurrentAllocatedFiniteOrdinaryReservations.edgeRequests, Nat.add_zero]
  rw [charges] at bounded
  refine ⟨value, heap, middle, edgeWork.1, after, completed, used, rfl, first, second, actual,
    bounded.1, bounded.2.2.1, ?_, rfl, rfl, rfl, rfl⟩
  exact Nat.le_trans bounded.2.2.2 (by omega)

/-- The own returned optional-binder state is the exact split point for additive prefix charges. -/
theorem used_optional_charges_append (pair : Nat × Nat) (body : Value Symbol Guard) (before : Checked width)
    (good : Good before) (available : Available before.native.machine.heap body)
    (used : InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free)
    (symbol : Symbol) (guard : Guard) (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations guard) :
    let start : Control (EdgeValue Symbol Guard) :=
      .code (.optionalBinder pair body (fun value => .work (makeEdge symbol guard [value]) .pure))
    ∃ value middle result after,
      step start before = .yielded (.code (.work (makeEdge symbol guard [value]) .pure)) middle ∧
      Trace 2 start before (.code (.pure result)) after ∧ Good after ∧
      (chargesThrough 2 start before).1 =
        (chargesThrough 1 start before).1 +
          (chargesThrough 1 (.code (.work (makeEdge symbol guard [value]) .pure)) middle).1 ∧
      (chargesThrough 2 start before).2 =
        (chargesThrough 1 start before).2 +
          (chargesThrough 1 (.code (.work (makeEdge symbol guard [value]) .pure)) middle).2 := by
  obtain ⟨value, _heap, middle, result, after, _completed, _used, _same, first, _second, actual, goodAfter,
      _nodes, _edges, _nodeTable, _edgeTable, _domains, _operations⟩ :=
    used_optional_work pair body before good available used symbol guard field
  have earlier : Steps 1
      (.code (.optionalBinder pair body (fun value => .work (makeEdge symbol guard [value]) .pure))) before
      (.code (.work (makeEdge symbol guard [value]) .pure)) middle :=
    .cons _ _ _ _ _ _ 0 first (.refl _ _)
  have charges := charges_append earlier 1
  exact ⟨value, middle, result, after, first, actual, goodAfter, charges⟩

end MicroCFTA.AllocationTraceIndependentIntegration

#print axioms MicroCFTA.AllocationTraceIndependentIntegration.used_optional_work
#check @MicroCFTA.AllocationTraceIndependentIntegration.used_optional_work
#print axioms MicroCFTA.AllocationTraceIndependentIntegration.used_optional_charges_append
#check @MicroCFTA.AllocationTraceIndependentIntegration.used_optional_charges_append
