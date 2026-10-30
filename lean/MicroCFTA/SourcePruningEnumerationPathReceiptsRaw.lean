import MicroCFTA.SourcePruningEnumerationPathTraversalRaw
import MicroCFTA.SourcePruningEnumerationPathReceipts

/-!
# Paths in every retained captured edge state

Actual own preparation supplies the paths for the ordered child traversal.
Captured receipts preserve their cache states and every successful raw row.
-/
namespace MicroCFTA.SourcePruningEnumerationPathReceiptsRaw
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathPreparedOpaque (ReceiptPaths)
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

private theorem selected_stopped_raw_paths
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
      .stopped completedPrefix observation candidate) : ObservationPaths P observation := by
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
              | complete fragments reached saved after => rw [traversed] at observed; cases observed
              | stopped fragments current retained =>
                  rw [traversed] at observed
                  obtain ⟨rfl, rfl, rfl⟩ := SourcePruningEnumerationSelectedEdge.Result.stopped.inj observed
                  exact SourcePruningEnumerationChildTraversal.stopped_raw_paths checkEmpty r n p h k
                    (staged.map (fun input => (input.1, input.2.1))) caller middle queries
                    fragments current retained rowPaths.1 buckets traversed

/-- Every actual captured receipt retains its cache paths and all successful raw rows. -/
theorem captured_paths
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path) :
    (match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => True
      | some receipt => ReceiptPaths P receipt) ∧
    (match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | some (.stopped _ observation _) => ObservationPaths P observation
      | _ => True) := by
  refine ⟨SourcePruningEnumerationPathReceipts.captured_paths checkEmpty r n p h k target scs edge
    caller before queries paths inherited tails projected, ?_⟩
  unfold SourcePruningEnumerationCapturedEdge.run
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled => trivial
  | rejected reached saved after => trivial
  | stopped completedPrefix observation candidate =>
      exact selected_stopped_raw_paths checkEmpty r n p h k scs edge caller before queries
        paths inherited tails projected completedPrefix observation candidate selected
  | complete fragment reached saved after =>
      dsimp only
      cases finished : SourcePruningEnumerationFinalize.run
          reached.checked.native.machine.heap k target fragment after <;> trivial

end MicroCFTA.SourcePruningEnumerationPathReceiptsRaw
