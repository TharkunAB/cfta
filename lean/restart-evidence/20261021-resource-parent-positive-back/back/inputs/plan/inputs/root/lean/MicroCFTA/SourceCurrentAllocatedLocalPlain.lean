import MicroCFTA.SourceCurrentAllocatedLocalWorker
import MicroCFTA.SourceEqualityPartialInheritedPlainPass

/-!
# Literal local reduction with empty effective own equalities

The actual accessor and allocated precheck complete in their returned
operation state. Their only selected class list is empty. The literal
Scan, required-path, and class workers then need no positive bound.
Residual guards stay in the original value. No historical execution is
transferred. General recursive caller completion remains separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalPlain
open Language EqualityNormalize InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run

/-- Equality freedom belongs to the complete accessor, including positive guard extraction. -/
def OwnEmpty (loaded : Allocated) : Prop :=
  SourceCompactGuards.sourceEqualities
    (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) = some []

/-- Exact loaded readback transfers the original effective equality test. -/
theorem of_readback {original : Guard} {loaded : Allocated}
    (readback : SourceEqualityConjoinAllocation.readback loaded = original)
    (plain : SourceCompactGuards.sourceEqualities original = some []) : OwnEmpty loaded := by
  change SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback loaded) = some []
  rw [readback]
  exact plain

/-- A successful same-cache field load derives both own equality freedom and stored readiness. -/
theorem of_load (original : Guard) (before : Operations) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load original before.constraints = .ok (some loaded))
    (plain : SourceCompactGuards.sourceEqualities original = some []) :
    OwnEmpty loaded ∧ EqReady before.constraints loaded.stored := by
  have field := SourceEqualityConstraintFieldLookup.load_ready original before.constraints
    valid.constraints cached loaded found
  exact ⟨of_readback field.2 plain, field.1⟩

/-- Actual ready allocation selects unchanged, erasure, or the empty own class list. -/
theorem prefix_cases (loaded : Allocated) (inherited : EqValue) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (storedReady : EqReady before.constraints loaded.stored) (inheritedReady : EqReady before.constraints inherited)
    (plain : OwnEmpty loaded) :
    (runPrefix loaded.stored loaded.guard inherited before).1 = .ok .unchanged ∨
      (runPrefix loaded.stored loaded.guard inherited before).1 = .ok .emptyChildren ∨
      (runPrefix loaded.stored loaded.guard inherited before).1 = .ok (.classes []) := by
  obtain ⟨own, done, nextValid, ownReady, classes, growth⟩ :=
    SourceEqualityAccessorAllocation.equalities_correct loaded.stored loaded.guard before valid storedReady
  have emptyClasses : SourceEqualityInheritedPayload.classes own.payload = some [] := classes.trans plain
  have payload : own.payload = some [] := by
    cases own with
    | contradiction => simp [SourceEqualityInheritedPayload.classes, SourceEqualityConstraintAllocation.Value.payload] at emptyClasses
    | live identity records =>
        cases records with
        | nil => rfl
        | cons first rest => simp [SourceEqualityInheritedPayload.classes, SourceEqualityConstraintAllocation.Value.payload] at emptyClasses
  have checked := SourceEqualityPrecheckAllocation.precheck_correct own inherited _ nextValid ownReady
    (inheritedReady.grows growth.constraint_growth)
  have actual : (runPrefix loaded.stored loaded.guard inherited before).1 =
      SourceEqualityPrecheck.precheck (some []) inherited.payload := by
    simpa only [SourceEqualityPartialPrecheckAllocation.run, done, payload] using checked.1
  rcases SourceEqualityPartialInheritedPlainPass.precheck_cases inherited.payload with first | second | third
  · exact Or.inl (actual.trans first)
  · exact Or.inr (Or.inl (actual.trans second))
  · exact Or.inr (Or.inr (actual.trans third))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Empty selected records execute all three literal stages and retain the full state. -/
theorem empty_stages (g s r e p h m c n budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget [] values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before fourth memo := by
  simp only [SourceCurrentAllocatedLocalWorker.classes, SourceCurrentAllocatedLocalWorker.scan,
    SourceCurrentAllocatedRecordScanWorker.scan_nil, SourceCurrentAllocatedLocalWorker.Outcome.bind]
  have noPaths : SourceEqualitySelectedRequired.paths ([] : Constraints) = [] := by
    simp [SourceEqualitySelectedRequired.paths, canonicalClass]
  simp only [List.map_nil, noPaths, SourceCurrentAllocatedLocalWorker.required,
    SourceEqualityRequiredExecution.requireAll_identity, SourceCurrentAllocatedLocalWorker.pass,
    SourceCurrentAllocatedClassWorker.pass_nil]
  rfl

/-- Empty effective own equalities complete at every bound with the literal prefix return. -/
theorem complete (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded) :
    ∃ results,
      SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo =
        .done results (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo ∧
      (results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values) := by
  rcases prefix_cases loaded inherited before.operations valid storedReady inheritedReady plain with unchanged | erased | live
  · exact ⟨values, SourceCurrentAllocatedLocalWorker.reduce_unchanged
      g s r e p h m c n budget loaded inherited values before fourth memo unchanged, Or.inl rfl⟩
  · exact ⟨_, SourceCurrentAllocatedLocalWorker.reduce_emptyChildren
      g s r e p h m c n budget loaded inherited values before fourth memo erased, Or.inr rfl⟩
  · refine ⟨EqualityLeafProjectionRuntimeEmpty.propagate values, ?_,
      SourceEqualityPartialInheritedPlainPass.propagate_shape values⟩
    simpa only [SourceCurrentAllocatedLocalWorker.reduce, live, SourceCurrentAllocatedPrecheck.state] using
      empty_stages g s r e p h m c n budget values (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo

/-- Any supplied successful return has the same full state and original-or-erased shape. -/
theorem done_shape (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo) (results : List (Value Symbol Guard))
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded)
    (done : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after savedFourth saved) :
    after = SourceCurrentAllocatedPrecheck.state before loaded inherited ∧ savedFourth = fourth ∧ saved = memo ∧
      (results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values) := by
  obtain ⟨actual, completed, shape⟩ := complete g s r e p h m c n budget loaded inherited values before fourth memo
    valid storedReady inheritedReady plain
  cases completed.symm.trans done
  exact ⟨rfl, rfl, rfl, shape⟩

end MicroCFTA.SourceCurrentAllocatedLocalPlain
