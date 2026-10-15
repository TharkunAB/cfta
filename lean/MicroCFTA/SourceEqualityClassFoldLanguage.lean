import MicroCFTA.SourceEqualityClassFoldEffects

/-!
# Independent language bounds for the complete class right fold

Each class captures the current forest returned by the later classes.
Local actual target inclusion retains every term that satisfies that class.
The finite fold retains every term satisfying all selected classes. Final
empty propagation preserves its complete ordered forest language exactly.
-/
namespace MicroCFTA.SourceEqualityClassFoldLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualitySharedTargetState
open SourceEqualityClassFoldGraph SourceEqualityClassFoldEffects
open InternedGuardedLanguage (meaning)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))

include clearTrue topTrue conjoined

/-- A fresh class edit derives language bounds from its actual class-local target receipts. -/
theorem class_language {record values before results after}
    (trace : Class (width := width) emptyGuard conjoin clear top record values before results after)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (EqualityNormalize.ClassSat (.node symbol terms) record.paths → All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  cases trace with
  | edit actual =>
      exact SourceEqualitySharedClassEdits.language emptyGuard conjoin clear top record coherent active values before.machine.heap available closed
        holds ambient clearTrue topTrue conjoined actual
        (initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready (pure_keeps _ ready.semantic.ready)) symbol terms

/-- The ordered class fold narrows its input and retains every accepted term satisfying all its classes. -/
theorem fold_language {records values before results after}
    (trace : Fold (width := width) emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  induction trace with
  | nil => exact ⟨id, fun _ accepted => accepted⟩
  | cons tail head ih =>
      have first := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available closed
      have checked := fold_effects tail ready available closed
      have last := class_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined head
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) checked.1 checked.2.2.1 checked.2.2.2 symbol terms
      exact ⟨fun accepted => first.1 (last.1 accepted),
        fun satisfied accepted => last.2 (satisfied _ List.mem_cons_self)
          (first.2 (fun record member => satisfied record (List.mem_cons_of_mem _ member)) accepted)⟩

/-- The complete fold and final source propagation have identical membership on terms satisfying the selected classes. -/
theorem pass_language {records values before results after}
    (trace : Pass (width := width) emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  cases trace with
  | done fold =>
      rw [SourceEqualityEmptyPropagation.exact holds ambient]
      exact fold_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined fold coherent active ready available closed symbol terms

end MicroCFTA.SourceEqualityClassFoldLanguage
