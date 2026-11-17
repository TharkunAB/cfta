import MicroCFTA.SourcePruningEnumerationInvocationEventLedgerProducer

namespace MicroCFTA.SourcePruningEnumerationInvocationEventLedger
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
open SourcePruningEnumerationSharedEagerChildren (consumeSelected ordinaryNonterminal)
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

/- Note [Literal truth of every invocation event]
The proof uses one mutual induction on the three ledger relations.
Each local event receives its actual operation equation from that constructor.
Child and tuple cases retain the same event lists and their exact order.
No witness is selected from a separate derivation.
The worker wrapper obtains one ledger once and proves its events authentic.
AuthenticEvent records operation equations only.
It does not assert the truth of removed semantic constraints.
-/

theorem invocation_ledger_events_authentic
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    (∀ (policy : Policy) (scs : List Suspended) (incoming : Node) (caller : Caller width)
      (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
      (index : Nat) (output : Output) (exit : ChildExit width) (localIndex : Nat)
      (path : List Nat) (events : List (Event width)),
      ChildLedgerAt checkEmpty r n p h k edgesOf policy scs incoming caller before queries
        done stopped index output exit localIndex path events →
      ∀ event ∈ events, AuthenticEvent event) ∧
    (∀ (policy : Policy) (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
      (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (exit : TupleExit width) (localIndex : Nat)
      (path : List Nat) (position : Nat) (events : List (Event width)),
      ChildrenLedgerAt checkEmpty r n p h k edgesOf policy done stopped inputs caller before queries
        index output exit localIndex path position events →
      ∀ event ∈ events, AuthenticEvent event) ∧
    (∀ (policy : Policy) (consume : Receipt width → Result Output Reason width)
      (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (receipt : Receipt width) (consumerIndex : Nat)
      (path : List Nat) (events : List (Event width)),
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output receipt consumerIndex path events →
      ∀ event ∈ events, AuthenticEvent event)
 := by
  have shallowDoneCase
      {path : List Nat} {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (_observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ∀ event ∈ [Event.dispatch path checkEmpty r n p h k scs incoming caller before queries (.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting) (some after)], AuthenticEvent event := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact actual

  have shallowStoppedCase
      {path : List Nat} {scs : List Suspended} {incoming : Node} {caller : Caller width}
      {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {observation : Observation width} {candidate : Option Cached}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries = (observation, candidate))
      (_shape : ShallowStopped observation candidate)
      (_observed : (outputs (stopped observation candidate))[index]? = some output) :
      ∀ event ∈ [Event.dispatch path checkEmpty r n p h k scs incoming caller before queries observation candidate], AuthenticEvent event := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact actual

  have guardedLowerCase
      {path : List Nat} {events : List (Event width)} {parent incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildLedgerAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex path events)
      (childIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ events, AuthenticEvent event := by
    exact childIH

  have guardedElseCase
      {path : List Nat} {events : List (Event width)} {parent incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex path events)
      (childIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ events, AuthenticEvent event := by
    exact childIH

  have eagerFallbackCase
      {path : List Nat} {events : List (Event width)} {incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_fallback : ordinaryNonterminal scs incoming = false)
      (_child : ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex path events)
      (childIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ events, AuthenticEvent event := by
    exact childIH

  have eagerOrdinaryCase
      {path : List Nat} {events : List (Event width)} {incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (_ordinary : ordinaryNonterminal scs incoming = true)
      (_rowOrder : edgesOf incoming = attempted ++ edge :: remaining)
      (_past : scan (fun selected current capturedQueries captured =>
        SourcePruningEnumerationSharedChildVisitors.visitSelected
          (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (_rowRun : SourcePruningEnumerationSharedChildVisitors.visitSelected
        (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (_row : SelectedLedgerAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex path events)
      (_offset : index = earlier.length + rowIndex)
      (_observed : (outputs (done fragment reached saved after))[localIndex]? = some output)
      (rowIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ events, AuthenticEvent event := by
    exact rowIH

  have nilCase
      {path : List Nat} {position : Nat} {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (_observed : (outputs (done [] caller queries before))[index]? = some output) :
      ∀ event ∈ ([] : List (Event width)), AuthenticEvent event := by
    intro event member
    cases member

  have consDoneCase
      {path : List Nat} {position : Nat} {childEvents tailEvents : List (Event width)}
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (_child : ChildLedgerAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex (path ++ [position]) childEvents)
      (_tail : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex path (position + 1) tailEvents)
      (childIH : ∀ event ∈ childEvents, AuthenticEvent event)
      (tailIH : ∀ event ∈ tailEvents, AuthenticEvent event) :
      ∀ event ∈ childEvents ++ tailEvents, AuthenticEvent event := by
    intro event member
    rcases List.mem_append.mp member with first | last
    · exact childIH event first
    · exact tailIH event last

  have consStoppedCase
      {path : List Nat} {position : Nat} {childEvents : List (Event width)}
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (_child : ChildLedgerAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex (path ++ [position]) childEvents)
      (childIH : ∀ event ∈ childEvents, AuthenticEvent event) :
      ∀ event ∈ childEvents, AuthenticEvent event := by
    exact childIH

  have unhandledNoneCase
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      ∀ event ∈ [Event.prepare path scs edge caller before queries none], AuthenticEvent event := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact actual

  have unhandledManyCase
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      ∀ event ∈ [Event.prepare path scs edge caller before queries (some (first :: second :: rest))], AuthenticEvent event := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact actual

  have rejectedCase
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (_observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      ∀ event ∈ [Event.prepare path scs edge caller before queries (some [])], AuthenticEvent event := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact actual

  have singletonDoneCase
      {path : List Nat} {events : List (Event width)}
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex path 0 events)
      (childrenIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ ([Event.prepare path scs edge caller before queries (some [((symbol, staged, residual), middle)])] ++ (events ++ [Event.residual path residual (.node symbol fragments) reached saved after (SelectedEdge.finish residual (.node symbol fragments) after)])), AuthenticEvent event := by
    intro event member
    rcases List.mem_append.mp member with first | rest
    · have same := List.mem_singleton.mp first
      subst event
      exact actual
    · rcases List.mem_append.mp rest with child | last
      · exact childrenIH event child
      · have same := List.mem_singleton.mp last
        subst event
        rfl

  have singletonStoppedCase
      {path : List Nat} {events : List (Event width)}
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex path 0 events)
      (childrenIH : ∀ event ∈ events, AuthenticEvent event) :
      ∀ event ∈ ([Event.prepare path scs edge caller before queries (some [((symbol, staged, residual), middle)])] ++ events), AuthenticEvent event := by
    intro event member
    rcases List.mem_append.mp member with first | child
    · have same := List.mem_singleton.mp first
      subst event
      exact actual
    · exact childrenIH event child

  constructor
  · intro policy scs incoming caller before queries done stopped index output exit localIndex path events ledger
    exact ChildLedgerAt.rec
        (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
        (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
        (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
        @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
        @nilCase @consDoneCase @consStoppedCase
        @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase ledger
  · constructor
    · intro policy done stopped inputs caller before queries index output exit localIndex path position events ledger
      exact ChildrenLedgerAt.rec
          (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase ledger
    · intro policy consume scs edge caller before queries index output receipt consumerIndex path events ledger
      exact SelectedLedgerAt.rec
          (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ events _ => ∀ event ∈ events, AuthenticEvent event)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase ledger

theorem eager_selected_output_authentic_event_ledger
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (SourcePruningEnumerationSharedChildVisitors.visitSelected
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf)
      consume scs edge caller before queries))[index]? = some output) :
    ∃ (receipt : Receipt width) (consumerIndex : Nat) (events : List (Event width)),
      SelectedLedgerAt checkEmpty r n p h k edgesOf .eager consume scs edge caller before queries
        index output receipt consumerIndex [] events ∧
      (∀ event ∈ events, AuthenticEvent event) ∧
      ∃ (earlier later : List Output),
        outputs (SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf)
          consume scs edge caller before queries) = earlier ++ outputs (consume receipt) ++ later ∧
        (outputs (consume receipt))[consumerIndex]? = some output ∧
        index = earlier.length + consumerIndex
 := by
  obtain ⟨receipt, consumerIndex, events, ledger, earlier, later, whole, found, offset⟩ :=
    eager_selected_output_event_ledger checkEmpty r n p h k edgesOf consume scs edge caller before queries
      index output observed
  have authentic := (invocation_ledger_events_authentic checkEmpty r n p h k edgesOf).2.2
    .eager consume scs edge caller before queries index output receipt consumerIndex [] events ledger
  exact ⟨receipt, consumerIndex, events, ledger, authentic, earlier, later, whole, found, offset⟩

end MicroCFTA.SourcePruningEnumerationInvocationEventLedger
