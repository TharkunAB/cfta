import MicroCFTA.SourcePruningEnumerationChildAncestryExtension
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Retained histories through actual ordered child traversal

Each actual child retains every key at every original slot.
The complete and stopped traces compose those concrete child observations.
The active expansion history remains equal to the traversal input history.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual completed trace retains all slot keys and the active expansion history. -/
theorem trace_ancestry_extension
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments afterCaller after savedQueries) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  induction trace with
  | nil => exact ⟨Extends.refl _, rfl⟩
  | cons head _tail ih =>
      have first := SourcePruningEnumerationChildDispatch.successful_ancestry_extension head
      exact ⟨first.1.trans ih.1, ih.2.trans first.2⟩

/-- Every observed complete traversal retains the histories from its own actual input. -/
theorem complete_ancestry_extension
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments afterCaller savedQueries after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry :=
  trace_ancestry_extension (complete_trace checkEmpty r n p h k inputs caller afterCaller before after
    queries savedQueries fragments completed)

/-- A stopped traversal retains the same histories at every actual attached cache. -/
theorem stopped_ancestry_extension
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller : Caller width} {before after : Cached} {queries : Queries}
    {completedPrefix : List Fragment} {observation : SourcePruningEnumerationChildDispatch.Observation width}
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation (some after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  obtain ⟨_consumed, value, bucket, _remaining, stoppedCaller, stoppedBefore, stoppedQueries,
    _decomposition, trace, actual⟩ :=
    stopped_trace checkEmpty r n p h k inputs caller before queries completedPrefix observation (some after) stopped
  have first := trace_ancestry_extension trace
  have last := SourcePruningEnumerationChildDispatch.observed_cache_ancestry_extension
    checkEmpty r n p h k bucket value stoppedCaller stoppedBefore stoppedQueries after (congrArg Prod.snd actual)
  exact ⟨first.1.trans last.1, last.2.trans first.2⟩

end MicroCFTA.SourcePruningEnumerationChildTraversal
