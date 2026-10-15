import MicroCFTA.SourceClosedGateComplete

/-!
# Finite closed source selection with both actual memo tables

Path induction constructs the selection graph at the current physical heap.
The closed-call receipts execute each reached predicate memo query. The
unfolding memo stays unchanged. No open-unfolding cost invariant is used.
-/
namespace MicroCFTA.SourceClosedGateSelection
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedSourceClassSelection (Trace selected select)
open SourceUnconstrainedMemo (Memo Correct)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every closed available forest derives finite stable source selection and both concrete memo receipts. -/
theorem complete (values : List (Value Symbol Guard)) (constraints : Constraints) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (closed : ClosedValues values)
    (unfolding : UMemo) (predicate : Memo) (correct : Correct state predicate) :
    ∃ bound queries saved, ∃ trace : Trace source values constraints state queries state,
      SourceMemoClassSelection.Reads values trace unfolding predicate unfolding saved ∧ Correct state saved ∧
      ∀ extra, select source (bound + extra) values constraints state = .done (some (selected queries)) state := by
  obtain ⟨queries, trace⟩ := SourceClosedGateComplete.selection source values constraints state facts available closed
  obtain ⟨saved, reads, kept⟩ := SourceClosedGateMemoSelection.selection trace facts available closed unfolding predicate correct
  obtain ⟨bound, done⟩ := InternedSourceClassSelection.trace_complete source values constraints state queries state trace
  exact ⟨bound, queries, saved, trace, reads, kept,
    fun extra => InternedSourceClassSelection.fuel_stable source bound extra values constraints state (selected queries) state done⟩

end MicroCFTA.SourceClosedGateSelection
