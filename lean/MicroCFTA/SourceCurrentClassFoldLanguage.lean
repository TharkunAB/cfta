import MicroCFTA.SourceCurrentClassEditLanguage
import MicroCFTA.SourceCurrentClassFoldComplete

/-!
# Independent language of the actual class fold with open siblings

Each class captures the forest returned by its actual completed tail.
Path-domain transport derives the next captured projection domains.
The fold narrows the original language and retains each accepted term
that satisfies all original classes. Final empty propagation is exact.
-/
namespace MicroCFTA.SourceCurrentClassFoldLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityProjectionPathDomain SourceCurrentClassFoldDomains
open InternedGuardedLanguage (meaning)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
variable (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))

include clearTrue topTrue conjoined

/-- The actual right fold narrows its forest and retains every accepted term satisfying all original classes. -/
theorem fold_language {records values results} {before after : NativeState width Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  induction actual with
  | nil => exact ⟨id, fun _ accepted => accepted⟩
  | cons tail head ih =>
      have first := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available
        (fun record member => domains record (List.mem_cons_of_mem _ member))
      have effects := fold_domains emptyGuard conjoin clear top tail
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available
        (fun record member => domains record (List.mem_cons_of_mem _ member))
      have last := SourceCurrentClassEditLanguage.class_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
        head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) effects.1 effects.2.2.1
        (fun path member => effects.2.2.2 _ (domains _ List.mem_cons_self path member)) symbol terms
      exact ⟨fun accepted => first.1 (last.1 accepted), fun satisfied accepted =>
        last.2 (satisfied _ List.mem_cons_self) (first.2 (fun record member => satisfied record (List.mem_cons_of_mem _ member)) accepted)⟩

/-- One completed source pass has the same bounds after its literal final propagation. -/
theorem pass_language {records values results} {before after : NativeState width Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  cases actual with
  | done fold =>
      rw [SourceEqualityEmptyPropagation.exact holds ambient]
      exact fold_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined fold coherent active ready available domains symbol terms

/-- Class-satisfying terms have identical input and output membership through the actual right fold. -/
theorem fold_exact_when_satisfied {records values results} {before after : NativeState width Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : ∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms := by
  have bounds := fold_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined actual coherent active ready available domains symbol terms
  exact ⟨bounds.1, bounds.2 satisfied⟩

/-- Class-satisfying terms have identical membership through the complete actual pass. -/
theorem exact_when_satisfied {records values results} {before after : NativeState width Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : ∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms := by
  have bounds := pass_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined actual coherent active ready available domains symbol terms
  exact ⟨bounds.1, bounds.2 satisfied⟩

/-- Reached range plans derive a finite stable actual pass with its independent language bounds. -/
theorem pass_complete {records values} {before : NativeState width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after, Pass emptyGuard conjoin clear top records values before results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ path : List Int, ForestClosed path values → ForestClosed path results) ∧
      SourceEqualityClassFoldWorkerProofs.StableRun
        (fun e p h c n => SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n records values before) results after ∧
      ∀ symbol terms,
        (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
          ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
            All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  obtain ⟨results, after, actual, finalReady, kept, resultAvailable, preserved, stable⟩ :=
    SourceCurrentClassFoldComplete.pass_complete emptyGuard conjoin clear top ranges coherent active ready available domains
  exact ⟨results, after, actual, finalReady, kept, resultAvailable, preserved, stable,
    pass_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined actual coherent active ready available domains⟩

end MicroCFTA.SourceCurrentClassFoldLanguage
