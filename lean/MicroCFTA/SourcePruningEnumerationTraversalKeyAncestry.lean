import MicroCFTA.SourcePruningEnumerationChildKeyAncestry
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Historical key shapes through actual ordered child traversal

Every completed child supplies the next original carrier.
The actual stopping child retains that carrier at every attached cache.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual completed trace retains the original historical key carrier. -/
theorem trace_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments afterCaller after savedQueries)
    (bounded : KeyAncestry carrier before.core) : KeyAncestry carrier after.core := by
  induction trace with
  | nil => exact bounded
  | cons head _tail ih =>
      exact ih (SourcePruningEnumerationChildDispatch.successful_key_ancestry bounded head)

/-- Every observed complete traversal retains the original historical key carrier. -/
theorem complete_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (bounded : KeyAncestry carrier before.core)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments afterCaller savedQueries after) : KeyAncestry carrier after.core :=
  trace_key_ancestry (complete_trace checkEmpty r n p h k inputs caller afterCaller before after
    queries savedQueries fragments completed) bounded

/-- Every actual stopped traversal with an attached cache retains the original carrier. -/
theorem stopped_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller : Caller width} {before after : Cached} {queries : Queries}
    {completedPrefix : List Fragment} {observation : SourcePruningEnumerationChildDispatch.Observation width}
    (bounded : KeyAncestry carrier before.core)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation (some after)) : KeyAncestry carrier after.core := by
  obtain ⟨_consumed, value, bucket, _remaining, stoppedCaller, stoppedBefore, stoppedQueries,
    _decomposition, trace, actual⟩ :=
    stopped_trace checkEmpty r n p h k inputs caller before queries completedPrefix observation (some after) stopped
  exact SourcePruningEnumerationChildDispatch.observed_cache_key_ancestry checkEmpty r n p h k bucket value
    stoppedCaller stoppedBefore stoppedQueries (trace_key_ancestry trace bounded) after (congrArg Prod.snd actual)

end MicroCFTA.SourcePruningEnumerationChildTraversal
