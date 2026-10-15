import MicroCFTA.SourceEqualityNativeDemandHeap
import MicroCFTA.SourceEqualityPartialNativeDemand

/-!
# Derived native heap effects in recursive result-memo scope

Current physical constructor inputs derive actual native heap preservation.
Current normalized equality fields derive actual operation-cache effects.
Together these receipts preserve the surrounding recursive result memo on
every finite outcome. No future heap or result-memo soundness is assumed.
The current input checks still need derivation from general compiled calls.
-/
namespace MicroCFTA.SourceEqualityPartialNativeHeap
open SourceEqualityNativeDemand SourceEqualityPartialNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Worker" => SourceEqualityPartialMemoWorker.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- Actual reached input checks derive the heap receipt and preserve every surrounding result cell. -/
theorem execute_sound [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fuel : Nat) (control : Control Output) (operations : Operations) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (ready : SourceEqualityRequiredCache.Ready worker.native.machine.heap)
    (fields : SourceEqualityNativeDemandOperations.FieldsThrough fuel control (input operations worker))
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control (input operations worker)) :
    let actual := execute fuel control (input operations worker)
    SourceEqualityRequiredCache.Keeps worker.native.machine.heap actual.state.native.machine.heap ∧
      SourceEqualityPartialMemoSound.Sound holds ambient (returned worker actual) := by
  have keeps := SourceEqualityNativeDemandHeap.execute_keeps fuel control (input operations worker) ready inputs
  exact ⟨keeps, SourceEqualityPartialNativeDemand.execute_sound holds ambient fuel control operations worker
    valid same sound fields keeps⟩

/-- All finite observations retain operation caches, native structure, outer keys, and outer cell meanings. -/
theorem execute_receipts [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fuel : Nat) (control : Control Output) (operations : Operations) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (shape : SourceRecursiveIntersectionNative.Shape worker.native)
    (ready : SourceEqualityRequiredCache.Ready worker.native.machine.heap)
    (fields : SourceEqualityNativeDemandOperations.FieldsThrough fuel control (input operations worker))
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control (input operations worker)) :
    let actual := execute fuel control (input operations worker)
    SourceEqualityConstraintMemoAllocation.Valid actual.state.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows operations actual.state.operations ∧
      SourceRecursiveIntersectionNative.Shape actual.state.native ∧
      SourceEqualityNativeDemandMemo.Retained worker.native actual.state.native ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (returned worker actual)) ∧
      SourceEqualityRequiredCache.Keeps worker.native.machine.heap actual.state.native.machine.heap ∧
      SourceEqualityPartialMemoSound.Sound holds ambient (returned worker actual) := by
  have frame := SourceEqualityPartialNativeDemand.execute_receipts fuel control operations worker
    valid same sound.valid shape fields
  have preserved := execute_sound holds ambient fuel control operations worker valid same sound ready fields inputs
  exact ⟨frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2, preserved⟩

end MicroCFTA.SourceEqualityPartialNativeHeap
