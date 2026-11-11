import MicroCFTA.SourcePruningEnumerationSharedChildProper

/-!
# Proper paths through actual shared child traversals

The actual completed trace preserves proper stored pending paths.
A stopped traversal retains that invariant at its attached candidate.
The proofs use current input buckets and literal child observations.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem trace_proper
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments reached after saved) :
    ProperState before.core → (∀ input ∈ inputs, ProperInputs input.2) → ProperState after.core := by
  induction trace with
  | nil => exact fun proper _ => proper
  | cons head _tail ih =>
      intro proper inputs
      apply ih
      · exact ChildDispatch.successful_proper proper (inputs _ List.mem_cons_self) head
      · intro input member
        exact inputs input (List.mem_cons_of_mem _ member)

/-- Every literal completed shared traversal preserves proper stored paths. -/
theorem complete_proper
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragments : List Fragment) (proper : ProperState before.core)
    (buckets : ∀ input ∈ inputs, ProperInputs input.2)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments reached saved after) :
    ProperState after.core :=
  trace_proper (complete_trace checkEmpty r n p h k inputs caller reached before after queries saved
    fragments completed) proper buckets

/-- An attached stopping candidate retains the invariant through the actual completed prefix. -/
theorem stopped_candidate_proper
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before after : Cached) (queries : Queries)
    (completedPrefix : List Fragment) (observation : ChildDispatch.Observation width)
    (proper : ProperState before.core) (buckets : ∀ input ∈ inputs, ProperInputs input.2)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation (some after)) :
    ProperState after.core := by
  obtain ⟨consumed, value, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
    shape, trace, head⟩ :=
    stopped_trace checkEmpty r n p h k inputs caller before queries completedPrefix observation (some after) stopped
  have prefixBuckets : ∀ input ∈ consumed, ProperInputs input.2 := by
    intro input member
    apply buckets input
    rw [shape]
    exact List.mem_append.mpr (.inl member)
  have nextBucket : ProperInputs bucket := by
    apply buckets (value, bucket)
    rw [shape]
    exact List.mem_append.mpr (.inr List.mem_cons_self)
  exact ChildDispatch.observed_cache_proper checkEmpty r n p h k bucket value stoppedCaller
    stoppedBefore stoppedQueries (trace_proper trace proper prefixBuckets) nextBucket after
    (congrArg Prod.snd head)

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
