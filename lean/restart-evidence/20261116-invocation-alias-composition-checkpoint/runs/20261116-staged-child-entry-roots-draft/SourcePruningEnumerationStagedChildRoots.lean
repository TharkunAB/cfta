import MicroCFTA.SourcePruningEnumerationStagedChildInvocation
import MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth

namespace MicroCFTA.SourcePruningEnumerationStagedChildRoots
open SourcePruningEnumerationSharedInvocationTrace
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Done" => Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "Stopped" => Observation width → Option Cached → Result Output Reason width
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
set_option autoImplicit false

/- Note [Roots at the selected child entry]
An old self-alias contains a finite root path for its raw variable.
Preserving every old alias therefore preserves totality.
The tuple proof carries that fact through each actual completed head.
It constructs Roots for the SAME child entry returned by the prefix induction.
It does not infer sufficient search fuel or construct a source model.
-/

theorem total_of_sameClass_forward
    (before after : UnionFind.Forest) (total : UnionFind.Total before)
    (kept : ∀ (left right : Nat), UnionFind.SameClass before left right →
      UnionFind.SameClass after left right) :
    UnionFind.Total after
 := by
  intro uv
  obtain ⟨root, size, path⟩ := total uv
  obtain ⟨afterRoot, afterSize, afterPath, _samePath⟩ := kept uv uv ⟨root, size, path, path⟩
  exact ⟨afterRoot, afterSize, afterPath⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem children_done_prefix_invocation_with_roots
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped)
    (priorInputs : List (Node × List Suspended)) (incoming : Node) (bucket : List Suspended)
    (rest : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (fragments : List Fragment)
    (finalCaller : Caller width) (finalQueries : Queries) (finalCache : Cached) (localIndex : Nat)
    (total : UnionFind.Total before.core.representatives)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped
      (priorInputs ++ (incoming, bucket) :: rest) caller before queries index output
      (.done fragments finalCaller finalQueries finalCache) localIndex) :
    ∃ (priorFragments : List Fragment) (childCaller : Caller width) (childBefore : Cached)
        (childQueries : Queries) (childRootIndex : Nat) (fragment : Fragment)
        (reached : Caller width) (saved : Queries) (after : Cached)
        (childCallbackIndex : Nat) (remainingFragments : List Fragment),
      priorFragments.length = priorInputs.length ∧
      fragments = priorFragments ++ fragment :: remainingFragments ∧
      ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming childCaller childBefore childQueries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun remaining => done (priorFragments ++ produced :: remaining))
            (fun completed => stopped (priorFragments ++ produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped priorFragments observation candidate)
        childRootIndex output (.done fragment reached saved after) childCallbackIndex ∧
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun remaining => done (priorFragments ++ fragment :: remaining))
        (fun completed => stopped (priorFragments ++ fragment :: completed)) rest reached after saved
        childCallbackIndex output (.done remainingFragments finalCaller finalQueries finalCache) localIndex ∧
      UnionFind.Total childBefore.core.representatives ∧
      ∃ (roots : Nat → Nat), EnumerationSchedule.Roots childBefore.core.representatives roots
 := by
  induction priorInputs generalizing done stopped caller before queries index fragments with
  | nil =>
    obtain ⟨fragment, reached, saved, after, childIndex, remaining,
        fragmentShape, child, tail⟩ :=
      children_done_head_invocation checkEmpty r n p h k edgesOf policy done stopped
        incoming bucket rest caller before queries index output fragments
        finalCaller finalQueries finalCache localIndex trace
    exact ⟨[], caller, before, queries, index, fragment, reached, saved, after,
      childIndex, remaining, rfl, fragmentShape, child, tail, total,
      EnumerationSchedule.roots_exist before.core.representatives total⟩
  | cons first prior ih =>
    rcases first with ⟨firstIncoming, firstBucket⟩
    obtain ⟨firstFragment, firstReached, firstSaved, firstAfter, firstIndex, tailFragments,
        firstShape, firstChild, firstTail⟩ :=
      children_done_head_invocation checkEmpty r n p h k edgesOf policy done stopped
        firstIncoming firstBucket (prior ++ (incoming, bucket) :: rest)
        caller before queries index output fragments finalCaller finalQueries finalCache localIndex trace
    have firstTotal : UnionFind.Total firstAfter.core.representatives := by
      apply total_of_sameClass_forward before.core.representatives firstAfter.core.representatives total
      exact SourcePruningEnumerationInvocationRawAliasGrowth.child_done_sameClass_forward
        checkEmpty r n p h k edgesOf policy firstBucket firstIncoming caller firstReached
        before firstAfter queries firstSaved _ _ index output firstFragment firstIndex firstChild
    obtain ⟨priorFragments, childCaller, childBefore, childQueries, childRootIndex,
        fragment, reached, saved, after, childCallbackIndex, remaining,
        priorLength, tailShape, child, tail, childTotal, childRoots⟩ :=
      ih (done := fun produced => done (firstFragment :: produced))
        (stopped := fun completed => stopped (firstFragment :: completed))
        (caller := firstReached) (before := firstAfter) (queries := firstSaved)
        (index := firstIndex) (fragments := tailFragments) firstTotal firstTail
    refine ⟨firstFragment :: priorFragments, childCaller, childBefore, childQueries,
      childRootIndex, fragment, reached, saved, after, childCallbackIndex, remaining,
      ?_, ?_, child, tail, childTotal, childRoots⟩
    · simp only [List.length_cons, priorLength]
    · calc
        fragments = firstFragment :: tailFragments := firstShape
        _ = (firstFragment :: priorFragments) ++ fragment :: remaining := by
          rw [tailShape]
          rfl

end MicroCFTA.SourcePruningEnumerationStagedChildRoots
