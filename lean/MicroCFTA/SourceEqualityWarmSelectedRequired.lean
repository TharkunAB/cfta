import MicroCFTA.SourceClosedGateSelection
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Finite selected and required stages at closed warm heaps

Closed gate progress uses path length and actual lookups. The actual
selection heap is unchanged. Required-path completion starts at that heap
and derives each returned physical invariant. No original source history,
unfolding cost heap, or completed prefix is an input premise.
-/
namespace MicroCFTA.SourceEqualityWarmSelectedRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedSourceClassSelection (Trace selected select)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Closed physical scope derives both finite stages, actual source memo calls, and the returned required-path heap. -/
theorem complete (values : List (Value Symbol Guard)) (constraints : Constraints) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∃ bound queries results after predicate,
      ∃ trace : SourceEqualitySelectedRequired.Execution source values constraints before queries before results after,
        SourceMemoClassSelection.Reads values trace.selection InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty
          InternedFreshOrdinaryUnfoldMemo.empty predicate ∧
        SourceUnconstrainedMemo.Correct before predicate ∧ Keeps before after ∧ SemanticReady after ∧
        Values after results ∧ ClosedValues results ∧
        (∀ extra, select source (bound + extra) values constraints before = .done (some (selected queries)) before) ∧
        SourceEqualityRequiredWorkerComplete.StableRun
          (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
            (SourceEqualitySelectedRequired.paths (selected queries)) values before) results after := by
  obtain ⟨bound, queries, predicate, selection, reads, correct, gateStable⟩ :=
    SourceClosedGateSelection.complete values constraints before semantic.ready.semantic.1.normal.facts available closed
      InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct before)
  obtain ⟨results, after, keeps, finalSemantic, resident, resultClosed, requiredStable, _⟩ :=
    SourceEqualityRequiredAPI.complete (SourceEqualitySelectedRequired.paths (selected queries)) values before
      (SourceEqualitySelectedRequired.paths_nonnegative _) semantic available closed
  obtain ⟨fuel, readFuel, enough⟩ := requiredStable
  have required := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨bound, queries, results, after, predicate, ⟨selection, fuel, readFuel, required⟩, reads, correct,
    keeps, finalSemantic, resident, resultClosed, gateStable, fuel, readFuel, enough⟩

end MicroCFTA.SourceEqualityWarmSelectedRequired
