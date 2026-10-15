import MicroCFTA.SourceEqualityAccessorAllocation
import MicroCFTA.SourceEqualityPartialAllocationFrame

/-!
# Original equality fields and accessor effects in recursive state

Normalized original fields derive stored physical values and literal
constructor receipts. Actual positive-guard and accessor allocation retains
the recursive result memo. Its own readback is the existing concrete source
accessor, not only a statement of equivalent constraint meaning.
-/
namespace MicroCFTA.SourceEqualityPartialAccessorAllocation
open SourceEqualityConstraintAllocation
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- An original normalized equality field derives ready storage and preserves every recursive result cell. -/
theorem construct_field (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (original : Option EqualityNormalize.Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (worker : SourceEqualityPartialMemoWorker.State width) (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    ∃ stored cache, construct original worker.constraints = (.ok stored, cache) ∧ Ready cache stored ∧
      SourceEqualityPhysicalPayload.read original = .ok stored.payload ∧
      SourceEqualityInheritedPayload.classes stored.payload = original ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityConstraintMemoAllocation.initial cache) ∧
      SourceEqualityPartialMemoSound.Sound holds ambient {worker with constraints := cache} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables {worker with constraints := cache}) := by
  obtain ⟨stored, cache, actual, cacheValid, ready, steps, read, classes⟩ :=
    construct_complete original cached worker.constraints sound.valid.1
  exact ⟨stored, cache, actual, ready, read, classes, SourceEqualityConstraintMemoAllocation.initial_valid cache cacheValid,
    SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker cache sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker cache sound.valid steps⟩

/-- Actual accessor execution gives literal own readback and preserves the complete recursive result memo. -/
theorem own_source (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (stored : Value) (guard : SourceGuards.Guard FullSyntax.Formula) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before) (ready : Ready before.constraints stored)
    (original : Option EqualityNormalize.Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload)
    (worker : SourceEqualityPartialMemoWorker.State width) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    ∃ result, (SourceEqualityAccessorAllocation.equalities stored guard before).1 = .ok result ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityAccessorAllocation.equalities stored guard before).2 ∧
      Ready (SourceEqualityAccessorAllocation.equalities stored guard before).2.constraints result ∧
      SourceEqualityPhysicalPayload.own (⟨original, guard⟩ : Guard) = .ok result.payload ∧
      SourceEqualityPartialMemoSound.Sound holds ambient
        {worker with constraints := (SourceEqualityAccessorAllocation.equalities stored guard before).2.constraints} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables
          {worker with constraints := (SourceEqualityAccessorAllocation.equalities stored guard before).2.constraints}) := by
  obtain ⟨result, actual, afterValid, resultReady, _, growth⟩ :=
    SourceEqualityAccessorAllocation.equalities_correct stored guard before valid ready
  have read := SourceEqualityAccessorAllocation.own_of_equalities stored guard before valid ready original cached built result actual
  have originalClasses := read_classes original cached stored.payload built
  have steps : Cache.Steps worker.constraints (SourceEqualityAccessorAllocation.equalities stored guard before).2.constraints := by
    simpa only [same] using growth.constraints
  refine ⟨result, actual, afterValid, resultReady, ?_,
    SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps⟩
  simpa only [SourceEqualityAccessorAllocation.constraint, originalClasses] using read

end MicroCFTA.SourceEqualityPartialAccessorAllocation
