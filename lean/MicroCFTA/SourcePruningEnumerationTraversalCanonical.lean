import MicroCFTA.SourcePruningEnumerationChildCanonical

/-!
# Canonical stored tries through actual ordered child traces

Each actual successful child cache supplies the next child's input.
The validity premise concerns the original ordered input buckets.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState EnumerationSemantics EnumerationValidity InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual complete ordered trace retains canonical suspended tries. -/
theorem trace_canonical
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments afterCaller after savedQueries)
    (canonical : Canonical before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ValidSuspended bucket) :
    Canonical after.core := by
  induction trace with
  | nil => exact canonical
  | cons head _tail ih =>
      apply ih (SourcePruningEnumerationChildDispatch.successful_canonical (observed := head)
        canonical (valid _ _ (List.mem_cons_self)))
      intro incoming bucket member
      exact valid incoming bucket (List.mem_cons_of_mem _ member)

/-- An observed complete traversal derives its own trace and preserves canonical stored tries. -/
theorem complete_canonical
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller afterCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragments : List Fragment}
    (canonical : Canonical before.core)
    (valid : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ValidSuspended bucket)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments afterCaller savedQueries after) : Canonical after.core :=
  trace_canonical (complete_trace checkEmpty r n p h k inputs caller afterCaller before after
    queries savedQueries fragments completed) canonical valid

end MicroCFTA.SourcePruningEnumerationChildTraversal
