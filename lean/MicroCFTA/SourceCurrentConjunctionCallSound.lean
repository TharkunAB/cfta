import MicroCFTA.SourceCurrentConjunctionCallRetained
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionMemo

set_option autoImplicit false
open scoped Classical

/-!
# Sound answers at actual current conjunction call endpoints

The actual completed call yields its checked semantic receipt. The original
Context supplies the ready heap and the correctness of the earlier memo.
Failed calls retain the earlier memo at their actual returned heap.
-/
namespace MicroCFTA.SourceCurrentConjunctionCallSound
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Context" => SourceCurrentAllocatedPartialInvariant.Context

/-- Retain the original endpoint facts and prove correctness of the actual returned memo. -/
theorem call_correct {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width)
    (memos : EndpointMemoGateTrace.Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    (At formulas solver inventory actual.state ∧
      SourceCurrentMemoMergeEffects.Stored actual.state.native.machine.heap before.merge ∧
      SourceCurrentEmptinessMemo.Correct formulas solver actual.state.native.machine.heap before.fourth) ∧
    SourceCurrentEmptinessMemo.Correct formulas solver actual.state.native.machine.heap actual.memo ∧
    (match (generalizing := false) actual with
      | .done answer _ _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer
      | .failed _ _ _ => True) := by
  have retained := SourceCurrentConjunctionCallRetained.call_retained
    p h budget query before memos context available closed
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked
    context.ready.good context.ready.semantic context.ready.costs
  refine ⟨retained, ?_⟩
  cases running : SourceCurrentConjunctionWorker.call p h budget before.fourth query
      (physical before.checked) with
  | done output after =>
    obtain ⟨answer, saved⟩ := output
    have actual := SourceCurrentConjunctionWorkerCompletion.call_sound p h budget
      before.fourth query (physical before.checked) answer after saved running
    have semantic := SourceCurrentConjunctionMemo.verified formulas solver actual ready available context.correct
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, running,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedConjunctionWorker.Outcome.memo, advancePhysical,
      SourceRecursiveIntersectionThunks.advance] using
      (show SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer from
          ⟨semantic.2.1, semantic.2.2.1⟩)
  | failed fault after =>
    simp only [SourceCurrentAllocatedConjunctionWorker.call, running,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state] at retained
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, running,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using
      (show SourceCurrentEmptinessMemo.Correct formulas solver
        (advancePhysical before.checked after).native.machine.heap before.fourth ∧ True from
          ⟨retained.2.2, trivial⟩)

end MicroCFTA.SourceCurrentConjunctionCallSound
