import MicroCFTA.SourcePruningEnumerationPathTerminal
import MicroCFTA.SourcePruningEnumerationPathOuter

/-!
# Stored paths through actual ordered child prefixes

Every completed prefix preserves the same original path predicate.
Every retained stopping candidate also preserves that predicate.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual completed child prefix preserves the fixed input path predicate. -/
theorem Trace.paths
    (trace : Trace (width := width) checkEmpty r n p h k inputs caller before queries
      fragments reached after saved)
    (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2) : StatePaths P after.core := by
  revert paths buckets
  induction trace with
  | nil => intro paths _; exact paths
  | @cons value bucket rest beforeCaller middleCaller afterCaller before middle after
      queries middleQueries afterQueries fragment fragments outer waiting head tail ih =>
      intro paths buckets
      have middlePaths := SourcePruningEnumerationChildDispatch.observed_cache_paths
        checkEmpty r n p h k bucket value beforeCaller before queries paths
        (buckets (value, bucket) List.mem_cons_self) middle (congrArg Prod.snd head)
      exact ih middlePaths (fun input member => buckets input (List.mem_cons_of_mem _ member))

/-- A complete actual traversal preserves paths at its exact final cache. -/
theorem complete_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragments : List Fragment) (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments reached saved after) : StatePaths P after.core :=
  (complete_trace checkEmpty r n p h k inputs caller reached before after queries saved
    fragments completed).paths paths buckets

/-- An actual stopped traversal preserves paths at every retained stopping cache. -/
theorem stopped_candidate_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (completedPrefix : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
    (candidate : Option Cached) (after : Cached) (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation candidate)
    (retained : candidate = some after) : StatePaths P after.core := by
  obtain ⟨consumed, value, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
      same, trace, called⟩ := stopped_trace checkEmpty r n p h k inputs caller before queries
        completedPrefix observation candidate stopped
  have prefixBuckets : ∀ input ∈ consumed, BucketPaths P input.2 := by
    intro input member
    apply buckets input
    rw [same]
    exact List.mem_append.mpr (.inl member)
  have stoppedPaths := trace.paths paths prefixBuckets
  have stoppedBucket : BucketPaths P bucket := by
    apply buckets (value, bucket)
    rw [same]
    exact List.mem_append.mpr (.inr List.mem_cons_self)
  exact SourcePruningEnumerationChildDispatch.observed_cache_paths checkEmpty r n p h k
    bucket value stoppedCaller stoppedBefore stoppedQueries stoppedPaths stoppedBucket after
    ((congrArg Prod.snd called).trans retained)

/-- The raw observation at an actual stop preserves paths even without an attached cache. -/
theorem stopped_outer_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (completedPrefix : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
    (candidate : Option Cached) (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation candidate) : StatePaths P observation.2.2.2.1 := by
  obtain ⟨consumed, value, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
      same, trace, called⟩ := stopped_trace checkEmpty r n p h k inputs caller before queries
        completedPrefix observation candidate stopped
  have prefixBuckets : ∀ input ∈ consumed, BucketPaths P input.2 := by
    intro input member
    apply buckets input
    rw [same]
    exact List.mem_append.mpr (.inl member)
  have stoppedPaths := trace.paths paths prefixBuckets
  have stoppedBucket : BucketPaths P bucket := by
    apply buckets (value, bucket)
    rw [same]
    exact List.mem_append.mpr (.inr List.mem_cons_self)
  have outerPaths := SourcePruningEnumerationChildDispatch.run_outer_paths checkEmpty r n p h k
    bucket value stoppedCaller stoppedBefore stoppedQueries stoppedPaths stoppedBucket
  rw [called] at outerPaths
  exact outerPaths

/-- A stopped raw singleton result preserves paths without an attached-cache premise. -/
theorem stopped_returned_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (completedPrefix : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
    (candidate : Option Cached) (fragment : Fragment) (reachedCaller : Caller width)
    (savedQueries : Queries) (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation candidate)
    (returnedObservation : observation =
      (.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting)) :
    StatePaths P returned := by
  obtain ⟨consumed, value, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
      same, trace, called⟩ := stopped_trace checkEmpty r n p h k inputs caller before queries
        completedPrefix observation candidate stopped
  have prefixBuckets : ∀ input ∈ consumed, BucketPaths P input.2 := by
    intro input member
    apply buckets input
    rw [same]
    exact List.mem_append.mpr (.inl member)
  have stoppedPaths := trace.paths paths prefixBuckets
  have stoppedBucket : BucketPaths P bucket := by
    apply buckets (value, bucket)
    rw [same]
    exact List.mem_append.mpr (.inr List.mem_cons_self)
  exact SourcePruningEnumerationChildDispatch.returned_paths checkEmpty r n p h k bucket value
    stoppedCaller reachedCaller stoppedBefore stoppedQueries savedQueries fragment returned outer waiting
    stoppedPaths stoppedBucket ((congrArg Prod.fst called).trans returnedObservation)

/-- Every actual traversal outcome retains paths in its observed outer state and cache. -/
theorem run_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (buckets : ∀ input ∈ inputs, BucketPaths P input.2) :
    match run checkEmpty r n p h k inputs caller before queries with
    | .complete _ _ _ after => StatePaths P after.core
    | .stopped _ observation candidate =>
        StatePaths P observation.2.2.2.1 ∧
        ∀ after, candidate = some after → StatePaths P after.core := by
  cases observed : run checkEmpty r n p h k inputs caller before queries with
  | complete fragments reached saved after =>
      exact complete_paths checkEmpty r n p h k inputs caller reached before after queries saved
        fragments paths buckets observed
  | stopped completedPrefix observation candidate =>
      exact ⟨stopped_outer_paths checkEmpty r n p h k inputs caller before queries
        completedPrefix observation candidate paths buckets observed,
        fun after retained => stopped_candidate_paths checkEmpty r n p h k inputs caller before queries
          completedPrefix observation candidate after paths buckets observed retained⟩

end MicroCFTA.SourcePruningEnumerationChildTraversal
