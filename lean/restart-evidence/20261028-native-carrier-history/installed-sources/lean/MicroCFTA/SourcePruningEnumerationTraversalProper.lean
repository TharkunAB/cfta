import MicroCFTA.SourcePruningEnumerationChildProper

/-!
# Proper pending paths through actual ordered child traces

Each actual successful child cache supplies the next child's input.
The proper-input premise concerns the original ordered buckets.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState EnumerationSemantics EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual complete ordered trace retains proper suspended tries. -/
theorem trace_proper
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments afterCaller after savedQueries)
    (proper : ProperState before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket) :
    ProperState after.core := by
  induction trace with
  | nil => exact proper
  | cons head _tail ih =>
      apply ih (SourcePruningEnumerationChildDispatch.successful_proper (observed := head)
        proper (valid _ _ (List.mem_cons_self)))
      intro incoming bucket member
      exact valid incoming bucket (List.mem_cons_of_mem _ member)

/-- An observed complete traversal derives its own trace and preserves proper stored tries. -/
theorem complete_proper
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (proper : ProperState before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments afterCaller savedQueries after) : ProperState after.core :=
  trace_proper (complete_trace checkEmpty r n p h k inputs caller afterCaller before after
    queries savedQueries fragments completed) proper valid

end MicroCFTA.SourcePruningEnumerationChildTraversal
