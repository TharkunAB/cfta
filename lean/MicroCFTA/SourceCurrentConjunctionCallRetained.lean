import MicroCFTA.SourceCurrentConjunctionWorkerEffects
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

set_option autoImplicit false
open scoped Classical

/-! Retained inventory and memo fields at actual call endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionCallRetained
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Context" => SourceCurrentAllocatedPartialInvariant.Context

private theorem insert_extends (memo : Memo) (query : Node) (answer : Bool)
    (absent : memo query.referenceOf = none) :
    SourceCurrentEmptinessMemo.Extends memo (SourceCurrentEmptinessMemo.insert memo query answer) := by
  intro key entry found
  by_cases same : key = query.referenceOf
  · subst key
    rw [absent] at found
    cases found
  · simpa only [SourceCurrentEmptinessMemo.insert, ite_eq_right same] using found

/-- Both actual outcomes retain every earlier fourth-table entry. -/
theorem call_fourth_extends {width : Nat} (p h budget : Nat) (query : Node)
    (before : Checked width) (memo : Memo) :
    SourceCurrentEmptinessMemo.Extends memo
      (SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo).memo := by
  cases present : memo query.referenceOf with
  | some entry =>
    rcases entry with ⟨original, answer⟩
    simp only [SourceCurrentAllocatedConjunctionWorker.call, SourceCurrentConjunctionWorker.call,
      present, SourceCurrentAllocatedConjunctionWorker.Outcome.memo]
    exact fun _ _ found => found
  | none =>
    cases actual : SourceCurrentConjunctionWorker.decision p h budget query (physical before) with
    | done answer after =>
      simp only [SourceCurrentAllocatedConjunctionWorker.call, SourceCurrentConjunctionWorker.call,
        present, actual, SourceCurrentConjunctionWorker.Outcome.bind,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo]
      exact insert_extends memo query answer present
    | failed fault after =>
      simp only [SourceCurrentAllocatedConjunctionWorker.call, SourceCurrentConjunctionWorker.call,
        present, actual, SourceCurrentConjunctionWorker.Outcome.bind,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo]
      exact fun _ _ found => found

private theorem physical_retained {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {before : Caller width} {memos : EndpointMemoGateTrace.Memos}
    (context : Context formulas solver inventory before memos) (after : Physical)
    (growth : Grows before.checked.native.machine.heap after.heap)
    (history : Extends before.checked.native.machine.heap.nodes.issued after.heap.nodes.issued) :
    At formulas solver inventory (advancePhysical before.checked after) ∧
      SourceCurrentMemoMergeEffects.Stored after.heap before.merge ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap before.fourth := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨context.admitted.contextual.nodes, context.admitted.contextual.edges⟩,
      ⟨context.admitted.covered.nodes, context.admitted.covered.edges⟩,
      grows_trans context.admitted.growth growth, extends_trans context.admitted.history history⟩
  · intro key entry found
    obtain ⟨identity, original, result, closed⟩ := context.stored key entry found
    exact ⟨identity, original.grows _ _ growth history, result.grows _ _ growth history, closed⟩
  · intro key input answer found
    obtain ⟨identity, available, sound⟩ := context.correct key input answer found
    exact ⟨identity, available.grows _ _ growth history, sound⟩

/-- Actual heap effects retain inventory admission and both old completed tables. -/
theorem call_retained {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    At formulas solver inventory actual.state ∧
      SourceCurrentMemoMergeEffects.Stored actual.state.native.machine.heap before.merge ∧
      SourceCurrentEmptinessMemo.Correct formulas solver actual.state.native.machine.heap before.fourth := by
  have effects := SourceCurrentConjunctionWorkerEffects.call_effects p h budget before.fourth query
    (physical before.checked) context.ready.semantic.ready.semantic context.ready.semantic.ready.covered available closed
  cases actual : SourceCurrentConjunctionWorker.call p h budget before.fourth query (physical before.checked) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at effects
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state]
    exact physical_retained context after effects.2.2.1 effects.2.2.2
  | failed fault after =>
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at effects
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state]
    exact physical_retained context after effects.2.2.1 effects.2.2.2

/-- A failed actual call retains correctness of its returned unchanged fourth table. -/
theorem call_failed_correct {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    match actual with
    | .done _ _ _ => True
    | .failed _ after saved => SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved := by
  have retained := call_retained p h budget query before memos context available closed
  cases actual : SourceCurrentConjunctionWorker.call p h budget before.fourth query (physical before.checked) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual]
  | failed fault after =>
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state] at retained
    simp only [SourceCurrentAllocatedConjunctionWorker.call, actual]
    exact retained.2.2

end MicroCFTA.SourceCurrentConjunctionCallRetained
