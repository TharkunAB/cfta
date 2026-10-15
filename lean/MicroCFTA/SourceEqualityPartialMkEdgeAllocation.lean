import MicroCFTA.SourceEqualityMkEdgeAllocation
import MicroCFTA.SourceEqualityPartialAllocationFrame

/-!
# Checked edge allocation in recursive result-memo state

The checked edge constructor retains accessor allocations and the selected
edge interner effects. The native domain and both native memo tables stay
in their current scope. Actual heap preservation retains every running
request and completed result cell with its current semantic proof.
-/
namespace MicroCFTA.SourceEqualityPartialMkEdgeAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (Valid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Worker" => SourceEqualityPartialMemoWorker.State

/-- Execute the source checked constructor with both actual returned state components. -/
noncomputable def run [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (symbol : Symbol) (stored : Value) (guard : SourceGuards.Guard FullSyntax.Formula)
    (children : List (InternedConstructorTemplates.Value Symbol Guard)) (before : OpState) (worker : Worker width) :
    Except String (InternedConstructorTemplates.EdgeValue Symbol Guard) × OpState × Worker width :=
  let built := SourceEqualityMkEdgeAllocation.build symbol stored guard children before worker.native.machine.heap
  (built.1, built.2.1, {worker with constraints := built.2.1.constraints, native := SourceEqualityNativeScoped.advanceHeap worker.native built.2.2})

/-- The selected edge receipt derives current Sound and preserves every original result cell. -/
theorem run_sound [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (stored : Value) (guard : SourceGuards.Guard FullSyntax.Formula)
    (children : List (InternedConstructorTemplates.Value Symbol Guard)) (before : OpState) (worker : Worker width)
    (valid : Valid before) (storedReady : Ready before.constraints stored) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (heapReady : SourceEqualityRequiredCache.Ready worker.native.machine.heap)
    (available : InternedNestedProvenance.Values worker.native.machine.heap children) :
    SourceEqualityPartialMemoSound.Sound holds ambient (run symbol stored guard children before worker).2.2 ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (run symbol stored guard children before worker).2.2) ∧
      Valid (run symbol stored guard children before worker).2.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (run symbol stored guard children before worker).2.1 := by
  obtain ⟨receipt, afterValid, growth⟩ :=
    SourceEqualityMkEdgeAllocation.build_receipt symbol stored guard children before worker.native.machine.heap valid storedReady
  have keeps := SourceEqualityMkEdgeAllocation.work_keeps symbol
    (SourceEqualityAccessorAllocation.constraint stored guard) children
    (SourceEqualityMkEdgeAllocation.accepted (SourceEqualityAccessorAllocation.constraint stored guard) children.length)
    worker.native.machine.heap heapReady available
  simp only [run, receipt]
  have steps : Cache.Steps worker.constraints (SourceEqualityMkEdgeAllocation.outputState (SourceEqualityMkEdgeAllocation.check stored guard children.length before).2
      (SourceEqualityMkEdgeAllocation.accepted (SourceEqualityAccessorAllocation.constraint stored guard) children.length)).constraints := by
    simpa only [same, receipt] using growth.constraints
  have allocated := SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps
  refine ⟨?_, SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps, ?_, ?_⟩
  · exact SourceEqualityPartialMemoSound.Sound.keeps holds ambient allocated rfl keeps
  · simpa only [receipt] using afterValid
  · simpa only [receipt] using growth

end MicroCFTA.SourceEqualityPartialMkEdgeAllocation
