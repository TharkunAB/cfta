import MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace MicroCFTA.WorkTraceIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A used optional binder produces the available child and literal width needed by the actual next Work step. -/
theorem optional_then_edge (pair : Nat × Nat) (body : Value Symbol Guard) (before : Checked width)
    (good : Good before) (available : Available before.native.machine.heap body)
    (used : InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free)
    (symbol : Symbol) (guard : Guard) (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations guard) :
    let start : Control (EdgeValue Symbol Guard) :=
      .code (.optionalBinder pair body (fun value => .work (makeEdge symbol guard [value]) .pure))
    ∃ value heap middle result after,
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap = .done value heap ∧
      InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free ∧
      step start before = .yielded (.code (.work (makeEdge symbol guard [value]) .pure)) middle ∧
      step (.code (.work (makeEdge symbol guard [value]) .pure)) middle = .yielded (.code (.pure result)) after ∧
      Trace 2 start before (.code (.pure result)) after ∧
      SourceCurrentAllocatedRecursiveMassTrace.InputsThrough 2 (initialBound before.native.machine.heap) start before ∧
      Good after ∧
      Stored (massAfter 2 (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit 2 (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit 2 (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + 2 ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ after.operations = before.operations ∧
      ∀ bits,
        before.native.machine.heap.nodes.next + credit 2 (initialBound before.native.machine.heap) < 2 ^ bits →
        before.native.machine.heap.edges.next + credit 2 (initialBound before.native.machine.heap) < 2 ^ bits →
        after.native.machine.heap.nodes.next < 2 ^ bits ∧ after.native.machine.heap.edges.next < 2 ^ bits := by
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
  let bound := initialBound before.native.machine.heap
  have positive : 1 ≤ SourceCurrentAllocatedRecursiveMassTrace.ceiling bound :=
    Nat.le_trans (InternedValueMassHeap.initial before.native.machine.heap good.native.machine.1).positive
      (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound)
  have width : 1 ≤ SourceCurrentAllocatedRecursiveMassTrace.listLimit (SourceCurrentAllocatedRecursiveMassTrace.ceiling bound) := by
    exact Nat.mul_le_mul positive positive
  have widths : SourceCurrentAllocatedRecursiveMassTrace.InputsThrough 2 bound start before := by
    refine ⟨trivial, ?_⟩
    rw [first]
    refine ⟨SourceRecursiveIntersectionWorkMass.Inputs.edge symbol guard [value] (by
      intro child member
      cases List.mem_singleton.mp member
      exact output) (by simpa only [List.length_singleton] using width), ?_⟩
    rw [second]
    trivial
  have bounded := SourceCurrentAllocatedRecursiveMassTrace.initial_prefix actual good fields widths
  refine ⟨value, heap, middle, edgeWork.1, after, completed, used, first, second, actual, widths,
    bounded.1, bounded.2.2.1, bounded.2.2.2.1, bounded.2.2.2.2.1, bounded.2.2.2.2.2, rfl, rfl, rfl, rfl, ?_⟩
  intro bits nodesRoom edgesRoom
  have nodes := bounded.2.2.2.1
  have edges := bounded.2.2.2.2.1
  omega

end MicroCFTA.WorkTraceIndependent

#print axioms MicroCFTA.WorkTraceIndependent.optional_then_edge
#check @MicroCFTA.WorkTraceIndependent.optional_then_edge
