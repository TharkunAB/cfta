import MicroCFTA.SourceEqualityConjoinAllocation
import MicroCFTA.SourceEqualityPartialAllocationFrame

/-!
# Concrete source conjunction in recursive result-memo state

Actual source structural guard order fixes conjunction. The completed
combination cache allocates only the raw stored equality fields. Its exact
constructor output and interner trace preserve all recursive result cells.
-/
namespace MicroCFTA.SourceEqualityPartialConjoinAllocation
open SourceEqualityConstraintAllocation
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Constraint" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Run raw source conjunction with the actual structural guard comparison. -/
noncomputable def run (first second : Constraint) (before : OpState) : Except String Constraint × OpState :=
  SourceEqualityConjoinAllocation.conjoin GuardStructuralOrder.le first second before

/-- Actual allocated output has literal complete source readback and preserves current recursive soundness. -/
theorem run_correct (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (first second : Constraint) (before : OpState) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (worker : SourceEqualityPartialMemoWorker.State width) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    ∃ result, (run first second before).1 = .ok result ∧
      SourceEqualityConstraintMemoAllocation.Valid (run first second before).2 ∧
      Ready (run first second before).2.constraints result.stored ∧
      SourceEqualityConjoinAllocation.readback result = SourceEqualityPCSNativeEdge.conjoin
        (SourceEqualityConjoinAllocation.readback first) (SourceEqualityConjoinAllocation.readback second) ∧
      SourceEqualityGuardReadback.Cached (SourceEqualityConjoinAllocation.readback result).equalities ∧
      SourceEqualityPhysicalPayload.read (SourceEqualityConjoinAllocation.readback result).equalities = .ok result.stored.payload ∧
      SourceEqualityPartialMemoSound.Sound holds ambient {worker with constraints := (run first second before).2.constraints} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables {worker with constraints := (run first second before).2.constraints}) := by
  obtain ⟨result, done, afterValid, resultReady, exact, cached, built, growth⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct GuardStructuralOrder.le first second before valid firstReady secondReady
  have steps : Cache.Steps worker.constraints (run first second before).2.constraints := by
    simpa only [same, run] using growth.constraints
  refine ⟨result, done, afterValid, resultReady, exact, cached, ?_,
    SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps⟩
  rw [exact]
  exact built

end MicroCFTA.SourceEqualityPartialConjoinAllocation
