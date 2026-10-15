import MicroCFTA.SourceEqualityClassFoldLanguage
import MicroCFTA.SourceEqualityClassFoldWorkerProofs

/-!
# Public finite class-fold execution and language contracts

Actual-prefix word checks derive finite source fold execution. Successful
checked workers and complete graphs agree. Larger bounds retain identical
forests and native states. Terms satisfying the selected classes survive.
-/
namespace MicroCFTA.SourceEqualityClassFoldAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityClassFoldWorker SourceEqualityClassFoldWorkerProofs
open InternedGuardedLanguage (meaning)

/-- Completed stable executions determine one forest and one full native state. -/
theorem stable_unique {evaluation : Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard A} {first second : A}
    {afterFirst afterSecond : NativeState width Symbol Guard} (left : StableRun evaluation first afterFirst) (right : StableRun evaluation second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  obtain ⟨a, b, d, f, g, one⟩ := left
  obtain ⟨aa, bb, dd, ff, gg, two⟩ := right
  exact Result.done.inj ((one (max a aa) (max b bb) (max d dd) (max f ff) (max g gg)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (two (max a aa) (max b bb) (max d dd) (max f ff) (max g gg)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Actual source fold graphs have unique ordered outputs and full native states. -/
theorem fold_unique {records values before first second afterFirst afterSecond}
    (left : Fold (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before first afterFirst)
    (right : Fold emptyGuard conjoin clear top records values before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (fold_stable emptyGuard conjoin clear top left) (fold_stable emptyGuard conjoin clear top right)

/-- Actual fold-and-propagate graphs have unique ordered outputs and full native states. -/
theorem pass_unique {records values before first second afterFirst afterSecond}
    (left : Pass (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before first afterFirst)
    (right : Pass emptyGuard conjoin clear top records values before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (pass_stable emptyGuard conjoin clear top left) (pass_stable emptyGuard conjoin clear top right)

/-- Checked complete source pass graphs and successful bounded workers agree in both directions. -/
theorem execution_iff (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before) (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) :
    Pass emptyGuard conjoin clear top records values before results after ↔
      ∃ e p h c n, pass emptyGuard conjoin clear top e p h c n records values before = .done results after := by
  constructor
  · intro trace
    obtain ⟨e, p, h, c, n, stable⟩ := pass_stable emptyGuard conjoin clear top trace
    exact ⟨e, p, h, c, n, stable e p h c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨e, p, h, c, n, done⟩
    exact pass_graph emptyGuard conjoin clear top e p h c n records values before ranges results after done

/-- Local reached request checks derive finite stable complete source class processing. -/
theorem complete (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, Pass emptyGuard conjoin clear top records values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      StableRun (fun e p h c n => pass emptyGuard conjoin clear top e p h c n records values before) results after := by
  obtain ⟨results, after, trace, checked⟩ := SourceEqualityClassFoldComplete.pass_complete emptyGuard conjoin clear top ranges ready available closed
  exact ⟨results, after, trace, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2, pass_stable emptyGuard conjoin clear top trace⟩

end MicroCFTA.SourceEqualityClassFoldAPI
