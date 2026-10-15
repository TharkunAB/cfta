import MicroCFTA.SourceEqualityGuardedEdgeSource

/-!
# Kernel checks for original guarded-edge reconstruction

A reflexive equality stays residual. Immediate source branches retain that
complete guard and the original symbol. The unchanged branch keeps each
original child; contradiction erases each position before reconstruction.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeExamples
open InternedConstructorTemplates SourceEqualityClassFoldGraph SourceObservations SourceSymbolicIndex
open SourceEqualityGuardedEdgeWorker
local notation "Symbol" => Label Unit
local notation "Guard" => Constraint Unit

private noncomputable instance : DecidableEq (Constraint Unit) := by classical exact inferInstance

/-- A reflexive source Same remains in the complete residual guard. -/
def residual : Guard := ⟨some [], .same [0] [0]⟩

/-- A literal source edge retains a mixed empty and unresolved child forest. -/
def original : EdgeValue Symbol Guard :=
  .mk ⟨7, ⟨("pair", ()), [.empty, .ref .depth], residual⟩⟩ [.empty, .reference .depth]

/-- Reflexive Same adds no physical equality class and is not discarded from the constraint. -/
theorem residual_payload : SourceEqualityPhysicalPayload.own residual = .ok (some []) := by cbv

/-- Empty own and inherited payloads preserve every original child and invoke the actual literal constructor. -/
theorem unchanged (before : NativeState width Symbol Guard) :
    SourceEqualityGuardedEdgeWorker.run (fun _ => true) residual (fun first _ => first) (fun _ => false) residual
      0 0 0 0 0 0 original (some []) before =
      let built := InternedConstructorTemplates.run (makeEdge original.entry.key.symbol residual original.children) before.machine.heap
      .done (.ok built.1) (SourceEqualityNativeScoped.advanceHeap before built.2) := by
  simp only [SourceEqualityGuardedEdgeWorker.run, original, EdgeValue.entry, EdgeValue.children, residual_payload, finish, SourceEqualityOnePassWorker.run,
    SourceEqualityOnePassWorker.runChecked, SourceEqualityPrecheck.empty_precheck]

/-- Inherited contradiction erases both positions before rebuilding the original complete guard. -/
theorem contradiction (before : NativeState width Symbol Guard) :
    SourceEqualityGuardedEdgeWorker.run (fun _ => true) residual (fun first _ => first) (fun _ => false) residual
      0 0 0 0 0 0 original none before =
      let built := InternedConstructorTemplates.run (makeEdge original.entry.key.symbol residual [.empty, .empty]) before.machine.heap
      .done (.ok built.1) (SourceEqualityNativeScoped.advanceHeap before built.2) := by
  simp only [SourceEqualityGuardedEdgeWorker.run, original, EdgeValue.entry, EdgeValue.children, residual_payload, finish, SourceEqualityOnePassWorker.run,
    SourceEqualityOnePassWorker.runChecked, SourceEqualityPrecheck.inherited_contradiction, EqualityLeafProjectionRuntimeEmpty.erase, List.map_cons, List.map_nil]

/-- Actual empty-heap interning retains literal fields, all children, and both native memo counters. -/
def Rebuilt : Result 8 Unit → Prop
  | .done (.ok result) after => result.entry.key.symbol = ("pair", ()) ∧ result.entry.key.constraint = residual ∧
      result.children = [.empty, .reference .depth] ∧ after.machine.heap.edges.next = 1 ∧ after.nodes.next = 0 ∧ after.edges.next = 0
  | _ => False

/-- Kernel reduction checks the source accessor, immediate pass, and actual final edge allocation. -/
theorem rebuilt : Rebuilt (SourceEqualityGuardedEdgeWorker.run (fun _ => true) residual (fun first _ => first) (fun _ => false) residual
    0 0 0 0 0 0 original (some []) (SourceEqualityNativeInitial.cold 8 empty)) := by cbv

end MicroCFTA.SourceEqualityGuardedEdgeExamples
