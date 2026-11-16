import MicroCFTA.SourcePruningEnumerationSharedInvocationInversions

namespace MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/- Note [Staged child invocation position]
The input prefix fixes the original staged child position.
Each completed head contributes one fragment to the same prefix.
Tuple constructors retain the actual child and tail invocations.
The proof follows those constructors and preserves both output indices.
It does not select another occurrence by output equality.
-/

private theorem children_cons_invocation_cases
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries) (index : Nat) (output : Output)
    (exit : TupleExit width) (localIndex : Nat)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped
      ((incoming, bucket) :: rest) caller before queries index output exit localIndex) :
    (∃ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
        (childIndex : Nat) (tailExit : TupleExit width),
      ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun remaining => done (produced :: remaining))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex ∧
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun remaining => done (fragment :: remaining))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output tailExit localIndex ∧ exit = TupleExit.prepend fragment tailExit) ∨
    (∃ (observation : Observation width) (candidate : Option Cached),
      ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun remaining => done (produced :: remaining))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex ∧
      exit = .stopped [] observation candidate) := by
  cases trace with
  | cons_done child tail =>
      exact Or.inl ⟨_, _, _, _, _, _, child, tail, rfl⟩
  | cons_stopped child =>
      exact Or.inr ⟨_, _, child, rfl⟩

theorem children_done_head_invocation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries) (index : Nat) (output : Output)
    (fragments : List Fragment) (finalCaller : Caller width) (finalQueries : Queries) (finalCache : Cached)
    (localIndex : Nat)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped
      ((incoming, bucket) :: rest) caller before queries index output
      (.done fragments finalCaller finalQueries finalCache) localIndex) :
    ∃ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
        (childIndex : Nat) (remainingFragments : List Fragment),
      fragments = fragment :: remainingFragments ∧
      ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun remaining => done (produced :: remaining))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex ∧
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun remaining => done (fragment :: remaining))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output (.done remainingFragments finalCaller finalQueries finalCache) localIndex := by
  rcases children_cons_invocation_cases checkEmpty r n p h k edgesOf policy done stopped
      incoming bucket rest caller before queries index output
      (.done fragments finalCaller finalQueries finalCache) localIndex trace with completed | interrupted
  · obtain ⟨fragment, reached, saved, after, childIndex, tailExit, child, tail, same⟩ := completed
    cases tailExit with
    | done remaining tailCaller tailQueries tailCache =>
        simp only [TupleExit.prepend] at same
        obtain ⟨fragmentsSame, callerSame, queriesSame, cacheSame⟩ := TupleExit.done.inj same
        subst finalCaller finalQueries finalCache
        exact ⟨fragment, reached, saved, after, childIndex, remaining, fragmentsSame, child, tail⟩
    | stopped earlier observation candidate =>
        simp only [TupleExit.prepend] at same
        cases same
  · obtain ⟨observation, candidate, _child, impossible⟩ := interrupted
    cases impossible

theorem children_done_prefix_invocation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped)
    (priorInputs : List (Node × List Suspended)) (incoming : Node) (bucket : List Suspended)
    (rest : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (fragments : List Fragment)
    (finalCaller : Caller width) (finalQueries : Queries) (finalCache : Cached) (localIndex : Nat)
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
        childCallbackIndex output (.done remainingFragments finalCaller finalQueries finalCache) localIndex := by
  induction priorInputs generalizing done stopped caller before queries index fragments with
  | nil =>
      obtain ⟨fragment, reached, saved, after, childIndex, remaining,
          fragmentShape, child, tail⟩ :=
        children_done_head_invocation checkEmpty r n p h k edgesOf policy done stopped
          incoming bucket rest caller before queries index output fragments
          finalCaller finalQueries finalCache localIndex trace
      exact ⟨[], caller, before, queries, index, fragment, reached, saved, after,
        childIndex, remaining, rfl, fragmentShape, child, tail⟩
  | cons first prior ih =>
      rcases first with ⟨firstIncoming, firstBucket⟩
      obtain ⟨firstFragment, firstReached, firstSaved, firstAfter, firstIndex, tailFragments,
          firstShape, _firstChild, firstTail⟩ :=
        children_done_head_invocation checkEmpty r n p h k edgesOf policy done stopped
          firstIncoming firstBucket (prior ++ (incoming, bucket) :: rest)
          caller before queries index output fragments finalCaller finalQueries finalCache localIndex trace
      obtain ⟨priorFragments, childCaller, childBefore, childQueries, childRootIndex,
          fragment, reached, saved, after, childCallbackIndex, remaining,
          priorLength, tailShape, child, tail⟩ :=
        ih (done := fun produced => done (firstFragment :: produced))
          (stopped := fun completed => stopped (firstFragment :: completed))
          (caller := firstReached) (before := firstAfter) (queries := firstSaved)
          (index := firstIndex) (fragments := tailFragments) firstTail
      refine ⟨firstFragment :: priorFragments, childCaller, childBefore, childQueries,
        childRootIndex, fragment, reached, saved, after, childCallbackIndex, remaining, ?_, ?_, child, tail⟩
      · simp only [List.length_cons, priorLength]
      · calc
          fragments = firstFragment :: tailFragments := firstShape
          _ = (firstFragment :: priorFragments) ++ fragment :: remaining := by
            rw [tailShape]
            rfl

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
