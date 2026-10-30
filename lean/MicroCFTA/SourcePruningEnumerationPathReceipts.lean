import MicroCFTA.SourcePruningEnumerationPathPreparedOpaque

/-!
# Paths in every actual captured edge receipt

The existing receipt predicate covers returned caches and stopped outer states.
A second law covers stopped raw singleton returned states without a candidate.
-/
namespace MicroCFTA.SourcePruningEnumerationPathReceipts
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathPreparedOpaque (ReceiptPaths)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem selected_stopped_paths
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    (completedPrefix : List Fragment)
    (observation : SourcePruningEnumerationChildDispatch.Observation width) (candidate : Option Cached)
    (observed : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
      .stopped completedPrefix observation candidate) :
    ReceiptPaths P (.stopped completedPrefix observation candidate) ∧
      ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries)
        (returned outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
        observation = (.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting) →
        StatePaths P returned := by
  unfold SourcePruningEnumerationSelectedEdge.run at observed
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none => rw [prepared] at observed; cases observed
  | some rows =>
      cases rows with
      | nil => rw [prepared] at observed; cases observed
      | cons row rest =>
          cases rest with
          | cons second rest => rw [prepared] at observed; cases observed
          | nil =>
              obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
              have rowPaths := prepare_paths paths inherited tails projected prepared
                ((symbol, staged, residual), middle) List.mem_cons_self
              have buckets : ∀ input ∈ staged.map (fun input => (input.1, input.2.1)),
                  BucketPaths P input.2 := by
                intro input member
                rcases List.mem_map.mp member with ⟨child, childMember, rfl⟩
                exact rowPaths.2 child childMember
              rw [prepared] at observed
              dsimp only at observed
              cases traversed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | complete fragments reached saved after =>
                  rw [traversed] at observed
                  cases observed
              | stopped fragments current retained =>
                  rw [traversed] at observed
                  obtain ⟨rfl, rfl, rfl⟩ := SourcePruningEnumerationSelectedEdge.Result.stopped.inj observed
                  have all := SourcePruningEnumerationChildTraversal.run_paths checkEmpty r n p h k
                    (staged.map (fun input => (input.1, input.2.1))) caller middle queries rowPaths.1 buckets
                  rw [traversed] at all
                  refine ⟨all, ?_⟩
                  intro fragment reached saved returned outer waiting returnedObservation
                  exact SourcePruningEnumerationChildTraversal.stopped_returned_paths checkEmpty r n p h k
                    (staged.map (fun input => (input.1, input.2.1))) caller middle queries
                    fragments current retained fragment reached saved returned outer waiting
                    rowPaths.1 buckets traversed returnedObservation

private theorem selected_rejected_paths
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (paths : StatePaths P before.core)
    (observed : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
      .rejected reached saved after) : StatePaths P after.core := by
  unfold SourcePruningEnumerationSelectedEdge.run at observed
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none => rw [prepared] at observed; cases observed
  | some rows =>
      cases rows with
      | nil =>
          rw [prepared] at observed
          obtain ⟨rfl, rfl, rfl⟩ := SourcePruningEnumerationSelectedEdge.Result.rejected.inj observed
          exact paths
      | cons row rest =>
          cases rest with
          | cons second rest => rw [prepared] at observed; cases observed
          | nil =>
              obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
              rw [prepared] at observed
              dsimp only at observed
              cases traversed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | complete fragments reached saved after => rw [traversed] at observed; cases observed
              | stopped fragments current retained => rw [traversed] at observed; cases observed

/-- Every actual captured receipt retains the same paths before callback or output tests. -/
theorem captured_paths
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    : match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => True
      | some receipt => ReceiptPaths P receipt := by
  unfold SourcePruningEnumerationCapturedEdge.run
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled => trivial
  | rejected reached saved after =>
      exact selected_rejected_paths checkEmpty r n p h k scs edge caller reached before after queries saved paths selected
  | stopped completedPrefix observation candidate =>
      exact (selected_stopped_paths checkEmpty r n p h k scs edge caller before queries
        paths inherited tails projected completedPrefix observation candidate selected).1
  | complete fragment reached saved after =>
      dsimp only
      have selectedPaths := SourcePruningEnumerationSelectedEdge.complete_paths checkEmpty r n p h k scs edge
        caller reached before after queries saved fragment paths inherited tails projected selected
      generalize finalized : SourcePruningEnumerationFinalize.run
        reached.checked.native.machine.heap k target fragment after = result
      cases result with
      | none => trivial
      | some finished =>
          exact SourcePruningEnumerationFinalize.run_paths reached.checked.native.machine.heap k target fragment
            after finished selectedPaths finalized

/-- A stopped raw singleton retains its paths even when no candidate cache is attached. -/
theorem captured_returned_paths
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    : match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | some (.stopped _ observation _) =>
          ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries)
            (returned outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
            observation = (.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting) →
            StatePaths P returned
      | _ => True := by
  unfold SourcePruningEnumerationCapturedEdge.run
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled => trivial
  | rejected reached saved after => trivial
  | stopped completedPrefix observation candidate =>
      exact (selected_stopped_paths checkEmpty r n p h k scs edge caller before queries
        paths inherited tails projected completedPrefix observation candidate selected).2
  | complete fragment reached saved after =>
      dsimp only
      cases finalized : SourcePruningEnumerationFinalize.run
          reached.checked.native.machine.heap k target fragment after <;> trivial

end MicroCFTA.SourcePruningEnumerationPathReceipts
