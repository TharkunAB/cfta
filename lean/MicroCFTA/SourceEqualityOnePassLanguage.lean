import MicroCFTA.SourceEqualityOnePassEffects
import MicroCFTA.SourceEqualityOnePassPrecheck

/-!
# Independent language of guarded native equality passes

The source pass narrows its input forest. Every accepted term satisfying
both original payloads survives. Contradiction follows from actual combined
normalization; live preservation follows from original physical classes.
-/
namespace MicroCFTA.SourceEqualityOnePassLanguage
open Language InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityOnePassGraph
open InternedGuardedLanguage (meaning)

private theorem erase_narrows (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) (EqualityLeafProjectionRuntimeEmpty.erase values) terms → All₂ (meaning holds ambient) values terms := by
  cases values with
  | nil => exact id
  | cons value values =>
      intro accepted
      cases accepted with
      | cons first rest => simp only [meaning] at first

/-- Actual guarded source processing narrows its forest and retains all accepted terms satisfying both original payloads. -/
theorem language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {own inherited : SourceEqualityPrecheck.Constraint} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Execution unconstrained emptyGuard conjoin clear top own inherited values before (.ok results) after)
    (valid : SourceEqualityOnePassPrecheck.Valid own) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (SourceEqualityPrecheck.Sat (.node symbol terms) own → SourceEqualityPrecheck.Sat (.node symbol terms) inherited →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  cases trace with
  | unchanged => exact ⟨id, fun _ _ accepted => accepted⟩
  | emptyChildren actual =>
      exact ⟨erase_narrows holds ambient values terms, fun first second _ =>
        False.elim (SourceEqualityOnePassPrecheck.contradiction_rejects actual (.node symbol terms) ⟨first, second⟩)⟩
  | live actual stages =>
      have records := SourceEqualityOnePassPrecheck.live_valid actual valid
      have bounds := stages.language (fun record member => (records record member).1) (fun record member => (records record member).2)
        ready available closed holds ambient clearTrue topTrue conjoined symbol terms
      refine ⟨bounds.1, ?_⟩
      intro first _ accepted
      have satisfied := SourceEqualityOnePassPrecheck.live_satisfied actual (.node symbol terms) first
      apply bounds.2 _ accepted
      intro record member
      exact satisfied record.paths (List.mem_map.mpr ⟨record, (SourceEqualitySelectedRecords.sublist _ _).subset member, rfl⟩)

end MicroCFTA.SourceEqualityOnePassLanguage
