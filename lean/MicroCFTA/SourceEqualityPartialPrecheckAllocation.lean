import MicroCFTA.SourceEqualityPartialAccessorAllocation
import MicroCFTA.SourceEqualityPrecheckAllocation

/-!
# Actual accessor and native precheck allocation prefix

The own equality accessor precedes the native precheck. Both retain the
same completed operation tables and physical interner. Original constructor
receipts connect the prefix to literal source own readback. Its actual
allocation trace preserves every recursive result cell and semantic proof.
-/
namespace MicroCFTA.SourceEqualityPartialPrecheckAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Demand the source own payload and run the actual native guard with its returned operation state. -/
noncomputable def run (stored : Value) (guard : SourceGuards.Guard Formula) (inherited : Value) (before : State) :
    Except String SourceEqualityPrecheck.Branch × State :=
  let own := SourceEqualityAccessorAllocation.equalities stored guard before
  match own.1 with
  | .error message => (.error message, own.2)
  | .ok value => SourceEqualityPrecheckAllocation.precheck value inherited own.2

/-- The full source prefix derives its literal own payload, exact branch, and complete allocation receipt. -/
theorem run_correct (stored : Value) (guard : SourceGuards.Guard Formula) (inherited : Value) (before : State)
    (valid : Valid before) (storedReady : Ready before.constraints stored) (inheritedReady : Ready before.constraints inherited)
    (original : Option EqualityNormalize.Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload) :
    ∃ (own : Value) (branch : SourceEqualityPrecheck.Branch),
      SourceEqualityPhysicalPayload.own (⟨original, guard⟩ : SourceSymbolicIndex.Constraint Formula) = .ok own.payload ∧
      (run stored guard inherited before).1 = .ok branch ∧
      SourceEqualityPrecheck.precheck own.payload inherited.payload = .ok branch ∧
      Valid (run stored guard inherited before).2 ∧ Grows before (run stored guard inherited before).2 := by
  obtain ⟨own, ownDone, ownValid, ownReady, _, ownGrows⟩ :=
    SourceEqualityAccessorAllocation.equalities_correct stored guard before valid storedReady
  have ownRead := SourceEqualityAccessorAllocation.own_of_equalities stored guard before valid storedReady original cached built own ownDone
  have originalClasses := read_classes original cached stored.payload built
  have inheritedCurrent := inheritedReady.grows ownGrows.constraint_growth
  obtain ⟨branch, precheckDone, branchExact, afterValid, afterGrows⟩ :=
    SourceEqualityPrecheckAllocation.precheck_complete own inherited
      (SourceEqualityAccessorAllocation.equalities stored guard before).2 ownValid ownReady inheritedCurrent
  have actual : run stored guard inherited before = SourceEqualityPrecheckAllocation.precheck own inherited
      (SourceEqualityAccessorAllocation.equalities stored guard before).2 := by simp only [run, ownDone]
  rw [actual]
  refine ⟨own, branch, ?_, precheckDone, branchExact, afterValid, ?_⟩
  · simpa only [SourceEqualityAccessorAllocation.constraint, originalClasses] using ownRead
  · exact ⟨steps_trans ownGrows.constraints afterGrows.constraints,
      Cache.extends_trans ownGrows.combinations afterGrows.combinations,
      Cache.extends_trans ownGrows.descents afterGrows.descents⟩

/-- The actual completed prefix preserves running and returned result cells and their current meaning. -/
theorem run_sound (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (stored : Value) (guard : SourceGuards.Guard FullSyntax.Formula) (inherited : Value) (before : State)
    (valid : Valid before) (storedReady : Ready before.constraints stored) (inheritedReady : Ready before.constraints inherited)
    (original : Option EqualityNormalize.Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload)
    (worker : SourceEqualityPartialMemoWorker.State width) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    SourceEqualityPartialMemoSound.Sound holds ambient {worker with constraints := (run stored guard inherited before).2.constraints} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables {worker with constraints := (run stored guard inherited before).2.constraints}) := by
  obtain ⟨_, _, _, _, _, _, growth⟩ := run_correct stored guard inherited before valid storedReady inheritedReady original cached built
  have steps : Cache.Steps worker.constraints (run stored guard inherited before).2.constraints := by
    simpa only [same] using growth.constraints
  exact ⟨SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps⟩

end MicroCFTA.SourceEqualityPartialPrecheckAllocation
