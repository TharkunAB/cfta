import MicroCFTA.SourceEqualityNativeDemandMemo
import MicroCFTA.SourceEqualityNativeDemandMeaning
import MicroCFTA.SourceEqualityPartialAllocationFrame

/-!
# Native checked demand inside recursive result-memo scope

Actual native execution retains its equality-operation state on every
observation. Its atomic receipts preserve the surrounding recursive memo
and each original physical request key. Native completed-cell structure
and operation validity follow separately. Current outer Sound transports
through an actual heap-preservation receipt, without a future Sound premise.
-/
namespace MicroCFTA.SourceEqualityPartialNativeDemand
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Worker" => SourceEqualityPartialMemoWorker.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- Enter native demand with the current native scope and completed operation tables. -/
def input (operations : Operations) (worker : Worker width) : SourceEqualityNativeDemand.State width :=
  ⟨worker.native, operations⟩

/-- Every native observation returns its actual caches while retaining the surrounding recursive memo. -/
def returned (worker : Worker width) (outcome : Outcome width Output) : Worker width :=
  {worker with native := outcome.state.native, constraints := outcome.state.operations.constraints}

/-- Native demand preserves surrounding request keys and cells across every finite observation. -/
theorem execute_receipts [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (operations : Operations) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (memoValid : SourceEqualityPartialMemoFrame.Valid (SourceEqualityPartialMemoFrame.stateTables worker))
    (shape : SourceRecursiveIntersectionNative.Shape worker.native)
    (fields : SourceEqualityNativeDemandOperations.FieldsThrough fuel control (input operations worker)) :
    let actual := execute fuel control (input operations worker)
    SourceEqualityConstraintMemoAllocation.Valid actual.state.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows operations actual.state.operations ∧
      SourceRecursiveIntersectionNative.Shape actual.state.native ∧
      SourceEqualityNativeDemandMemo.Retained worker.native actual.state.native ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (returned worker actual)) := by
  have allocation := SourceEqualityNativeDemandOperations.execute_operations fuel control (input operations worker) valid fields
  have native := SourceEqualityNativeDemandMemo.execute_preserves fuel control (input operations worker) shape
  have steps : Cache.Steps worker.constraints (execute fuel control (input operations worker)).state.operations.constraints := by
    simpa only [same, input] using allocation.2.constraints
  exact ⟨allocation.1, allocation.2, native.1, native.2,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ memoValid steps⟩

/-- Actual native heap preservation transports all current outer cell proofs through actual allocation effects. -/
theorem execute_sound [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (fuel : Nat) (control : Control Output) (operations : Operations) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (fields : SourceEqualityNativeDemandOperations.FieldsThrough fuel control (input operations worker))
    (keeps : SourceEqualityRequiredCache.Keeps worker.native.machine.heap
      (execute fuel control (input operations worker)).state.native.machine.heap) :
    SourceEqualityPartialMemoSound.Sound holds ambient (returned worker (execute fuel control (input operations worker))) := by
  have allocation := SourceEqualityNativeDemandOperations.execute_constraint_steps fuel control (input operations worker) valid fields
  have steps : Cache.Steps worker.constraints (execute fuel control (input operations worker)).state.operations.constraints := by
    simpa only [same, input] using allocation
  have allocated := SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps
  exact SourceEqualityPartialMemoSound.Sound.keeps holds ambient allocated rfl keeps

end MicroCFTA.SourceEqualityPartialNativeDemand
