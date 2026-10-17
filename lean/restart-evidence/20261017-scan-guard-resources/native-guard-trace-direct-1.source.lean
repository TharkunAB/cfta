import MicroCFTA.SourceCurrentNativeGuardStep
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Initial finite guard bounds for checked native traces

Actual yielded instructions produce the next carrier and code checks.
Iteration uses the original alphabet and the literal trace length. A
separate initial count bound can enlarge the final finite alphabet.
-/
namespace MicroCFTA.SourceCurrentNativeGuardTrace
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeDemand
open SourceCurrentNativeGuardAlphabet (advance)
open SourceCurrentNativeGuardStep (Fields heap_mono fields_mono)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "Allocated" => SourceCurrentAllocatedNativeFieldClosure.Fields
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
variable {A : Type} {width fuel : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A physical trace constructs its own final carrier and captured code checks. -/
theorem prefix (alphabet : List Guard) {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (good : Good before) (allocated : Allocated control before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) (fields : Fields alphabet control) :
    Heap (fun guard => guard ∈ advance alphabet fuel) after.native.machine.heap ∧
      Fields (advance alphabet fuel) rest := by
  induction trace generalizing alphabet with
  | refl => exact ⟨known, fields⟩
  | cons control before middle current rest after count inputs one tail ih =>
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good inputs allocated
      have nextGood : Good current := by simpa only [one, Outcome.state] using effects.1
      have nextAllocated : Allocated middle current := by
        simpa only [one, SourceCurrentAllocatedNativeFieldClosure.OutcomeFields] using effects.2.2.2.2.2
      have nextHeap := SourceCurrentNativeGuardStep.step_heap alphabet control before good inputs known fields
      have reachedHeap : Heap (fun guard => guard ∈ alphabet) current.native.machine.heap := by
        simpa only [one, Outcome.state] using nextHeap
      have nextFields := SourceCurrentNativeGuardStep.yielded_fields alphabet control middle before current
        good inputs allocated known fields one
      exact ih (SourceCurrentNativeGuardAlphabet.step alphabet) nextGood nextAllocated
        (heap_mono (fun _ member => SourceCurrentNativeGuardAlphabet.mem_step_of_mem member) reachedHeap) nextFields

/-- An initial instruction ceiling bounds the same final heap and continuation carrier. -/
theorem bounded (alphabet : List Guard) (limit : Nat) {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (good : Good before) (allocated : Allocated control before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) (fields : Fields alphabet control)
    (count : fuel ≤ limit) :
    Heap (fun guard => guard ∈ advance alphabet limit) after.native.machine.heap ∧
      Fields (advance alphabet limit) rest := by
  have actual := prefix alphabet trace good allocated known fields
  have increase := SourceCurrentNativeGuardAlphabet.advance_count_mono alphabet count
  exact ⟨heap_mono increase actual.1, fields_mono increase rest actual.2⟩

end MicroCFTA.SourceCurrentNativeGuardTrace
