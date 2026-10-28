import MicroCFTA.SourcePruningEnumerationTraversalKeyAncestry
import MicroCFTA.SourcePruningEnumerationKeyAncestryOwnFinalize
import MicroCFTA.SourcePruningEnumerationCapturedEdge

/-!
# Historical key shapes through actual selected and captured heads

Own classes and ordered child traversal preserve the original carrier.
Residual recording and captured finalization add no historical keys.
Each exposed complete, rejected or stopped cache retains that carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual exposed selected-head cache retains the original historical key carrier. -/
theorem observed_cache_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller : Caller width} {before : Cached} {queries : Queries}
    {result : Result width}
    (bounded : KeyAncestry carrier before.core)
    (observed : run checkEmpty r n p h k scs edge caller before queries = result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after => KeyAncestry carrier after.core
    | .stopped _ _ (some after) => KeyAncestry carrier after.core
    | _ => True := by
  rw [← observed]
  unfold run
  cases own : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => trivial
  | some rows =>
      cases rows with
      | nil => exact bounded
      | cons row rest =>
          obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
          cases rest with
          | cons next later => trivial
          | nil =>
              have ownBounded : KeyAncestry carrier middle.core :=
                SourcePruningEnumerationCachedOwn.prepare_key_ancestry bounded own _
                  (List.mem_singleton_self _)
              dsimp only
              cases children : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped fragments observation candidate =>
                  cases candidate with
                  | none => trivial
                  | some after =>
                      exact SourcePruningEnumerationChildTraversal.stopped_key_ancestry ownBounded children
              | complete fragments reached saved after =>
                  exact finish_key_ancestry residual (.node symbol fragments) after
                    (SourcePruningEnumerationChildTraversal.complete_key_ancestry ownBounded children)

end MicroCFTA.SourcePruningEnumerationSelectedEdge

namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual finalization retains the original carrier at every exposed captured-head cache. -/
theorem observed_cache_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller : Caller width} {before : Cached} {queries : Queries}
    {result : Result width}
    (bounded : KeyAncestry carrier before.core)
    (observed : run checkEmpty r n p h k target scs edge caller before queries = some result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after => KeyAncestry carrier after.core
    | .stopped _ _ (some after) => KeyAncestry carrier after.core
    | _ => True := by
  unfold run at observed
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled | rejected | stopped =>
      simp only [selected] at observed
      cases observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_key_ancestry bounded selected
  | complete fragment reached saved middle =>
      simp only [selected] at observed
      obtain ⟨finished, finalized, same⟩ := Option.map_eq_some_iff.mp observed
      have middleBounded := SourcePruningEnumerationSelectedEdge.observed_cache_key_ancestry bounded selected
      have finishedBounded := SourcePruningEnumerationFinalize.run_key_ancestry
        reached.checked.native.machine.heap k target fragment middle finished middleBounded finalized
      cases same
      exact finishedBounded

end MicroCFTA.SourcePruningEnumerationCapturedEdge
