import MicroCFTA.SourcePruningEnumerationPathTraversal
import MicroCFTA.SourcePruningEnumerationPathObservationRaw

/-!
# Paths in every raw row at an actual child traversal stop

The completed prefix supplies the state at the actual stopping child.
The stopping observation retains paths in every successful raw row.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathObservationRaw (ObservationPaths)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every successful raw row at the actual traversal stop retains the input paths. -/
theorem stopped_raw_paths
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (completedPrefix : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
    (candidate : Option Cached) (paths : StatePaths P before.core)
    (buckets : ∀ input ∈ inputs, BucketPaths P input.2)
    (stopped : run checkEmpty r n p h k inputs caller before queries =
      .stopped completedPrefix observation candidate) : ObservationPaths P observation := by
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
  have rawPaths := SourcePruningEnumerationPathObservationRaw.child_paths checkEmpty r n p h k
    bucket value stoppedCaller stoppedBefore stoppedQueries stoppedPaths stoppedBucket
  rw [called] at rawPaths
  exact rawPaths

end MicroCFTA.SourcePruningEnumerationChildTraversal
