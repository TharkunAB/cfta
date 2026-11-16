import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
import MicroCFTA.SourcePruningEnumerationSharedChildRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationOwnAliasForest

namespace MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected)
open SourcePruningEnumerationSharedEagerChildren (consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
open SourcePruningEnumerationSharedInvocationTrace
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Raw aliases through indexed invocations]
The three motives follow the actual mutual invocation relations.
A completed exit retains every raw alias from that call's entry cache.
A stopped exit makes no alias claim.
The shallow case uses the actual successful ChildDispatch receipt.
Tuple cases compose the actual child endpoint with its actual tail.
Selected cases use the literal own preparation and residual finish.
An ordinary child uses the selected row's same captured cache.
No callback alias law, safety premise or future cache relation is assumed.
-/

private def Forward (before after : Cached) : Prop :=
  ∀ left right, UnionFind.SameClass before.core.representatives left right →
    UnionFind.SameClass after.core.representatives left right

private def ChildAliases (before : Cached) : ChildExit width → Prop
  | .done _ _ _ after => Forward before after
  | .stopped _ _ => True

private def TupleAliases (before : Cached) : TupleExit width → Prop
  | .done _ _ _ after => Forward before after
  | .stopped _ _ _ => True

private def SelectedAliases (before : Cached) : Receipt width → Prop
  | .complete _ _ _ after => Forward before after
  | _ => True

private theorem invocation_aliases
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    (∀ (policy : Policy) (scs : List Suspended) (incoming : Node) (caller : Caller width)
      (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
      (index : Nat) (output : Output) (exit : ChildExit width) (localIndex : Nat),
      ChildInvocationAt checkEmpty r n p h k edgesOf policy
        scs incoming caller before queries done stopped index output exit localIndex → ChildAliases before exit) ∧
    (∀ (policy : Policy) (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
      (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (exit : TupleExit width) (localIndex : Nat),
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        done stopped inputs caller before queries index output exit localIndex → TupleAliases before exit) ∧
    (∀ (policy : Policy) (consume : Receipt width → Result Output Reason width)
      (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (receipt : Receipt width) (consumerIndex : Nat),
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy
        consume scs edge caller before queries index output receipt consumerIndex → SelectedAliases before receipt) := by
  have shallowDoneCase
      {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (_observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ChildAliases before (.done fragment reached saved after) := by
    intro left right same
    exact ((SourcePruningEnumerationSharedChildRawAliasGrowth.successful_sameClass_forward
      (actual := actual)).2 left right same).2

  have shallowStoppedCase
      {scs : List Suspended} {incoming : Node} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped} {index : Nat} {output : Output}
      {observation : Observation width} {candidate : Option Cached}
      (_actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        (observation, candidate))
      (_shape : ShallowStopped observation candidate)
      (_observed : (outputs (stopped observation candidate))[index]? = some output) :
      ChildAliases before (.stopped observation candidate) := by
    exact True.intro

  have guardedLowerCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildAliases before exit) :
      ChildAliases before exit := by
    exact childIH

  have guardedElseCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildAliases before exit) :
      ChildAliases before exit := by
    exact childIH

  have eagerFallbackCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_fallback : ordinaryNonterminal scs incoming = false)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildAliases before exit) :
      ChildAliases before exit := by
    exact childIH

  have eagerOrdinaryCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (_ordinary : ordinaryNonterminal scs incoming = true)
      (_order : edgesOf incoming = attempted ++ edge :: remaining)
      (_past : scan (fun selected current capturedQueries captured =>
        visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (_rowRun : visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (_row : SelectedInvocationAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex)
      (_offset : index = earlier.length + rowIndex)
      (_observed : (outputs (done fragment reached saved after))[localIndex]? = some output)
      (rowIH : SelectedAliases before (.complete fragment reached saved after)) :
      ChildAliases before (.done fragment reached saved after) := by
    exact rowIH

  have nilCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (_observed : (outputs (done [] caller queries before))[index]? = some output) :
      TupleAliases before (.done [] caller queries before) := by
    exact fun _ _ same => same

  have consDoneCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex)
      (_tail : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex)
      (childIH : ChildAliases before (.done fragment reached saved after))
      (tailIH : TupleAliases after exit) :
      TupleAliases before (TupleExit.prepend fragment exit) := by
    cases exit with
    | done _fragments _reached _saved _after =>
        exact fun left right same => tailIH left right (childIH left right same)
    | stopped _completed _observation _candidate => exact True.intro

  have consStoppedCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex)
      (_childIH : ChildAliases before (.stopped observation candidate)) :
      TupleAliases before (.stopped [] observation candidate) := by
    exact True.intro

  have unhandledNoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedAliases (width := width) before .unhandled := by
    exact True.intro

  have unhandledManyCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedAliases (width := width) before .unhandled := by
    exact True.intro

  have rejectedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (_observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      SelectedAliases before (.rejected caller queries before) := by
    exact True.intro

  have singletonDoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex)
      (childrenIH : TupleAliases middle (.done fragments reached saved after)) :
      SelectedAliases before (.complete (.node symbol fragments) reached saved
        (SelectedEdge.finish residual (.node symbol fragments) after)) := by
    have forest := SourcePruningEnumerationOwnAliasForest.prepare_forest (actual := actual)
    intro left right same
    have atMiddle : UnionFind.SameClass middle.core.representatives left right := by
      rw [forest]
      exact same
    exact childrenIH left right atMiddle

  have singletonStoppedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex)
      (_childrenIH : TupleAliases middle (.stopped completed observation candidate)) :
      SelectedAliases before (.stopped completed observation candidate) := by
    exact True.intro

  constructor
  · intro policy scs incoming caller before queries done stopped index output exit localIndex trace
    exact ChildInvocationAt.rec
        (motive_1 := fun _ _ _ _ before _ _ _ _ _ exit _ _ => ChildAliases before exit)
        (motive_2 := fun _ _ _ _ _ before _ _ _ exit _ _ => TupleAliases before exit)
        (motive_3 := fun _ _ _ _ _ before _ _ _ receipt _ _ => SelectedAliases before receipt)
        @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
        @nilCase @consDoneCase @consStoppedCase
        @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
  · constructor
    · intro policy done stopped inputs caller before queries index output exit localIndex trace
      exact ChildrenInvocationAt.rec
          (motive_1 := fun _ _ _ _ before _ _ _ _ _ exit _ _ => ChildAliases before exit)
          (motive_2 := fun _ _ _ _ _ before _ _ _ exit _ _ => TupleAliases before exit)
          (motive_3 := fun _ _ _ _ _ before _ _ _ receipt _ _ => SelectedAliases before receipt)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
    · intro policy consume scs edge caller before queries index output receipt consumerIndex trace
      exact SelectedInvocationAt.rec
          (motive_1 := fun _ _ _ _ before _ _ _ _ _ exit _ _ => ChildAliases before exit)
          (motive_2 := fun _ _ _ _ _ before _ _ _ exit _ _ => TupleAliases before exit)
          (motive_3 := fun _ _ _ _ _ before _ _ _ receipt _ _ => SelectedAliases before receipt)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace

/-- A completed actual child invocation retains every raw entry alias. -/
theorem child_done_sameClass_forward
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (scs : List Suspended) (incoming : Node) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (done : Done) (stopped : Stopped)
    (index : Nat) (output : Output) (fragment : Fragment) (localIndex : Nat)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf policy
      scs incoming caller before queries done stopped index output
        (.done fragment reached saved after) localIndex) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass after.core.representatives left right := by
  exact (invocation_aliases checkEmpty r n p h k edgesOf).1
    policy scs incoming caller before queries done stopped index output
      (.done fragment reached saved after) localIndex trace

/-- A completed actual tuple invocation retains every raw entry alias. -/
theorem children_done_sameClass_forward
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (index : Nat) (output : Output) (fragments : List Fragment) (localIndex : Nat)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
      done stopped inputs caller before queries index output
        (.done fragments reached saved after) localIndex) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass after.core.representatives left right := by
  exact (invocation_aliases checkEmpty r n p h k edgesOf).2.1
    policy done stopped inputs caller before queries index output
      (.done fragments reached saved after) localIndex trace

/-- A completed actual selected invocation retains every raw entry alias. -/
theorem selected_complete_sameClass_forward
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy
      consume scs edge caller before queries index output
        (.complete fragment reached saved after) consumerIndex) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass after.core.representatives left right := by
  exact (invocation_aliases checkEmpty r n p h k edgesOf).2.2
    policy consume scs edge caller before queries index output
      (.complete fragment reached saved after) consumerIndex trace

end MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
