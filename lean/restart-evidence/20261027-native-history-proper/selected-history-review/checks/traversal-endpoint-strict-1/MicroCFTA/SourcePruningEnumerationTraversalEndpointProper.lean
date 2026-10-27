import MicroCFTA.SourcePruningEnumerationTraversalProper

/-!
# Proper paths at actual complete and stopped child endpoints

The exact completed prefix supplies the stopped child's input cache.
The stopped child supplies its own attached cache.
An absent cache has no invariant conclusion.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A stopped traversal preserves proper paths at its actual attached endpoint. -/
theorem stopped_proper
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller : Caller width} {before after : Cached} {queries : Queries}
    {fragments : List Fragment} {observation : SourcePruningEnumerationChildDispatch.Observation width}
    (proper : ProperState before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped fragments observation (some after)) : ProperState after.core := by
  obtain ⟨consumed, incoming, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
    decomposition, trace, observed⟩ :=
    stopped_trace checkEmpty r n p h k inputs caller before queries fragments observation (some after) stopped
  have prefixProper : ProperState stoppedBefore.core := by
    apply trace_proper trace proper
    intro value retained member
    apply valid value retained
    rw [decomposition]
    exact List.mem_append_left _ member
  have bucketProper : ProperInputs bucket := by
    apply valid incoming bucket
    rw [decomposition]
    exact List.mem_append_right _ (List.mem_cons_self)
  exact SourcePruningEnumerationChildDispatch.observed_cache_proper checkEmpty r n p h k bucket incoming
    stoppedCaller stoppedBefore stoppedQueries prefixProper bucketProper after
    (by simpa only [observed] using rfl)

/-- Every actual traversal result preserves proper paths at each retained endpoint. -/
theorem observed_cache_proper
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller : Caller width} {before : Cached} {queries : Queries}
    (proper : ProperState before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket)
    {result : Result width}
    (observed : run checkEmpty r n p h k inputs caller before queries = result) :
    match result with
    | .complete _ _ _ after => ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | .stopped _ _ none => True := by
  cases result with
  | complete fragments afterCaller savedQueries after =>
      exact complete_proper proper valid observed
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some after => exact stopped_proper proper valid observed

end MicroCFTA.SourcePruningEnumerationChildTraversal
