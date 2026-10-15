import MicroCFTA.SourceEqualityClassFoldEffects

/-!
# Finite source class folds from actual reached request checks

Fresh class completion uses local target and native request progress.
Every earlier class plan refers to an actual completed tail. Induction on
the finite class list derives the fold and its one final propagation.
-/
namespace MicroCFTA.SourceEqualityClassFoldComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualitySharedTargetState
open SourceEqualityClassFoldGraph SourceEqualityClassFoldEffects

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Local reached word checks derive a complete class with initially unforced target slots. -/
theorem class_complete (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : ClassRanges emptyGuard conjoin clear top record values before) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, Class emptyGuard conjoin clear top record values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready (pure_keeps _ ready.semantic.ready)
  obtain ⟨results, after, actual, _⟩ := SourceEqualitySharedEditAPI.list_complete emptyGuard conjoin clear top record values before.machine.heap available closed
    ranges (SourceEqualitySharedClassEdits.compiled_allowed record) initialReady available closed
  have trace : Class emptyGuard conjoin clear top record values before results after.native := .edit actual
  exact ⟨results, _, trace, class_effects trace ready available closed⟩

/-- Actual completed tail checks derive every class and the complete finite source right fold. -/
theorem fold_complete {records values} {before : NativeState width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, Fold emptyGuard conjoin clear top records values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  induction ranges with
  | nil => exact ⟨_, _, .nil, ready, pure_keeps _ ready.semantic.ready, available, closed⟩
  | cons tail head ih =>
      obtain ⟨middle, next, first, nextReady, firstKeeps, firstAvailable, firstClosed⟩ := ih ready available closed
      obtain ⟨results, after, last, finalReady, lastKeeps, resultAvailable, resultClosed⟩ :=
        class_complete emptyGuard conjoin clear top _ middle next (head middle next first) nextReady firstAvailable firstClosed
      exact ⟨results, after, .cons first last, finalReady, firstKeeps.trans lastKeeps, resultAvailable, resultClosed⟩

/-- Finite local request checks derive the complete fold and final source empty propagation. -/
theorem pass_complete {records values} {before : NativeState width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, Pass emptyGuard conjoin clear top records values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  obtain ⟨results, after, fold, checked⟩ := fold_complete emptyGuard conjoin clear top ranges ready available closed
  have trace : Pass emptyGuard conjoin clear top records values before (EqualityLeafProjectionRuntimeEmpty.propagate results) after := .done fold
  exact ⟨_, after, trace, pass_effects trace ready available closed⟩

end MicroCFTA.SourceEqualityClassFoldComplete
