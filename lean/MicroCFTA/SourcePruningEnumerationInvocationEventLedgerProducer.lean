import MicroCFTA.SourcePruningEnumerationInvocationEventLedger

namespace MicroCFTA.SourcePruningEnumerationInvocationEventLedger
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected)
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Construct one invocation ledger]
The proof uses mutual induction on the three existing invocation traces.
Each handler builds one strengthened ledger constructor from actual calls.
The private motives ignore the proof value and retain its visible indices.
They do not identify hidden data by proof irrelevance.
The returned ledger is the single bundle used by later consumers.
All list witnesses are constructed in Prop. No trace is eliminated into Type.
The actual eager trace producer discharges the child policy internally.
The supplied whole-output and terminal callback indices do not change.
-/

private def ChildCovered (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    {policy : Policy} {scs : List Suspended} {incoming : Node} {caller : Caller width}
    {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
    {index : Nat} {output : Output} {exit : ChildExit width} {localIndex : Nat}
    (_trace : ChildInvocationAt checkEmpty r n p h k edgesOf policy scs incoming caller before queries
      done stopped index output exit localIndex) : Prop :=
    ∀ path, ∃ events, ChildLedgerAt checkEmpty r n p h k edgesOf policy scs incoming caller before queries
      done stopped index output exit localIndex path events

private def TupleCovered (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    {policy : Policy} {done : TupleDone} {stopped : TupleStopped} {inputs : List (Node × List Suspended)}
    {caller : Caller width} {before : Cached} {queries : Queries}
    {index : Nat} {output : Output} {exit : TupleExit width} {localIndex : Nat}
    (_trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped inputs caller before queries
      index output exit localIndex) : Prop :=
    ∀ path position, ∃ events, ChildrenLedgerAt checkEmpty r n p h k edgesOf policy done stopped inputs caller before queries
      index output exit localIndex path position events

private def SelectedCovered (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    {policy : Policy} {consume : Receipt width → Result Output Reason width}
    {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
    {index : Nat} {output : Output} {receipt : Receipt width} {consumerIndex : Nat}
    (_trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
      index output receipt consumerIndex) : Prop :=
    ∀ path, ∃ events, SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
      index output receipt consumerIndex path events

theorem invocation_event_ledgers
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    (∀ (policy : Policy) (scs : List Suspended) (incoming : Node) (caller : Caller width)
      (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
      (index : Nat) (output : Output) (exit : ChildExit width) (localIndex : Nat),
      ChildInvocationAt checkEmpty r n p h k edgesOf policy scs incoming caller before queries
        done stopped index output exit localIndex →
      ∀ path, ∃ events, ChildLedgerAt checkEmpty r n p h k edgesOf policy
        scs incoming caller before queries done stopped index output exit localIndex path events) ∧
    (∀ (policy : Policy) (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
      (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (exit : TupleExit width) (localIndex : Nat),
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped inputs caller before queries
        index output exit localIndex →
      ∀ path position, ∃ events, ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        done stopped inputs caller before queries index output exit localIndex path position events) ∧
    (∀ (policy : Policy) (consume : Receipt width → Result Output Reason width)
      (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (receipt : Receipt width) (consumerIndex : Nat),
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output receipt consumerIndex →
      ∀ path, ∃ events, SelectedLedgerAt checkEmpty r n p h k edgesOf policy
        consume scs edge caller before queries index output receipt consumerIndex path events)
 := by
  have shallowDoneCase
      {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.shallow_done (stopped := stopped) actual observed) := by
    intro path
    exact ⟨_, ChildLedgerAt.shallow_done actual observed⟩

  have shallowStoppedCase
      {scs : List Suspended} {incoming : Node} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped} {index : Nat} {output : Output}
      {observation : Observation width} {candidate : Option Cached}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        (observation, candidate))
      (shape : ShallowStopped observation candidate)
      (observed : (outputs (stopped observation candidate))[index]? = some output) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.shallow_stopped (done := done) actual shape observed) := by
    intro path
    exact ⟨_, ChildLedgerAt.shallow_stopped actual shape observed⟩

  have guardedLowerCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (childTrace : ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCovered checkEmpty r n p h k edgesOf childTrace) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.guarded_lower lower childTrace) := by
    intro path
    obtain ⟨events, childLedger⟩ := childIH path
    exact ⟨events, ChildLedgerAt.guarded_lower lower childLedger⟩

  have guardedElseCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (childTrace : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCovered checkEmpty r n p h k edgesOf childTrace) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.guarded_else lower childTrace) := by
    intro path
    obtain ⟨events, childLedger⟩ := childIH path
    exact ⟨events, ChildLedgerAt.guarded_else lower childLedger⟩

  have eagerFallbackCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (fallback : ordinaryNonterminal scs incoming = false)
      (childTrace : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCovered checkEmpty r n p h k edgesOf childTrace) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.eager_fallback fallback childTrace) := by
    intro path
    obtain ⟨events, childLedger⟩ := childIH path
    exact ⟨events, ChildLedgerAt.eager_fallback fallback childLedger⟩

  have eagerOrdinaryCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (ordinary : ordinaryNonterminal scs incoming = true)
      (rowOrder : edgesOf incoming = attempted ++ edge :: remaining)
      (past : scan (fun selected current capturedQueries captured =>
        visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (rowRun : visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (rowTrace : SelectedInvocationAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex)
      (offset : index = earlier.length + rowIndex)
      (observed : (outputs (done fragment reached saved after))[localIndex]? = some output)
      (rowIH : SelectedCovered checkEmpty r n p h k edgesOf rowTrace) :
      ChildCovered checkEmpty r n p h k edgesOf (ChildInvocationAt.eager_ordinary (stopped := stopped) ordinary rowOrder past rowRun rowTrace offset observed) := by
    intro path
    obtain ⟨events, rowLedger⟩ := rowIH path
    exact ⟨events, ChildLedgerAt.eager_ordinary ordinary rowOrder past rowRun rowLedger offset observed⟩

  have nilCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (observed : (outputs (done [] caller queries before))[index]? = some output) :
      TupleCovered checkEmpty r n p h k edgesOf (ChildrenInvocationAt.nil (policy := policy) (stopped := stopped) observed) := by
    intro path position
    exact ⟨[], ChildrenLedgerAt.nil observed⟩

  have consDoneCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (childTrace : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex)
      (tailTrace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex)
      (childIH : ChildCovered checkEmpty r n p h k edgesOf childTrace)
      (tailIH : TupleCovered checkEmpty r n p h k edgesOf tailTrace) :
      TupleCovered checkEmpty r n p h k edgesOf (ChildrenInvocationAt.cons_done childTrace tailTrace) := by
    intro path position
    obtain ⟨childEvents, childLedger⟩ := childIH (path ++ [position])
    obtain ⟨tailEvents, tailLedger⟩ := tailIH path (position + 1)
    exact ⟨childEvents ++ tailEvents, ChildrenLedgerAt.cons_done childLedger tailLedger⟩

  have consStoppedCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (childTrace : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex)
      (childIH : ChildCovered checkEmpty r n p h k edgesOf childTrace) :
      TupleCovered checkEmpty r n p h k edgesOf (ChildrenInvocationAt.cons_stopped childTrace) := by
    intro path position
    obtain ⟨events, childLedger⟩ := childIH (path ++ [position])
    exact ⟨events, ChildrenLedgerAt.cons_stopped childLedger⟩

  have unhandledNoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedCovered checkEmpty r n p h k edgesOf (SelectedInvocationAt.unhandled_none (queries := queries) (policy := policy) (consume := consume) actual observed) := by
    intro path
    exact ⟨_, SelectedLedgerAt.unhandled_none actual observed⟩

  have unhandledManyCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedCovered checkEmpty r n p h k edgesOf (SelectedInvocationAt.unhandled_many (queries := queries) (policy := policy) (consume := consume) actual observed) := by
    intro path
    exact ⟨_, SelectedLedgerAt.unhandled_many actual observed⟩

  have rejectedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      SelectedCovered checkEmpty r n p h k edgesOf (SelectedInvocationAt.rejected (policy := policy) (consume := consume) actual observed) := by
    intro path
    exact ⟨_, SelectedLedgerAt.rejected actual observed⟩

  have singletonDoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (childrenTrace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex)
      (childrenIH : TupleCovered checkEmpty r n p h k edgesOf childrenTrace) :
      SelectedCovered checkEmpty r n p h k edgesOf (SelectedInvocationAt.singleton_done actual childrenTrace) := by
    intro path
    obtain ⟨events, childrenLedger⟩ := childrenIH path 0
    exact ⟨_, SelectedLedgerAt.singleton_done actual childrenLedger⟩

  have singletonStoppedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (childrenTrace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex)
      (childrenIH : TupleCovered checkEmpty r n p h k edgesOf childrenTrace) :
      SelectedCovered checkEmpty r n p h k edgesOf (SelectedInvocationAt.singleton_stopped actual childrenTrace) := by
    intro path
    obtain ⟨events, childrenLedger⟩ := childrenIH path 0
    exact ⟨_, SelectedLedgerAt.singleton_stopped actual childrenLedger⟩

  constructor
  · intro policy scs incoming caller before queries done stopped index output exit localIndex trace
    exact ChildInvocationAt.rec
        (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ trace => ChildCovered checkEmpty r n p h k edgesOf trace)
        (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ trace => TupleCovered checkEmpty r n p h k edgesOf trace)
        (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ trace => SelectedCovered checkEmpty r n p h k edgesOf trace)
        @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
        @nilCase @consDoneCase @consStoppedCase
        @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
  · constructor
    · intro policy done stopped inputs caller before queries index output exit localIndex trace
      exact ChildrenInvocationAt.rec
          (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ trace => ChildCovered checkEmpty r n p h k edgesOf trace)
          (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ trace => TupleCovered checkEmpty r n p h k edgesOf trace)
          (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ trace => SelectedCovered checkEmpty r n p h k edgesOf trace)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
    · intro policy consume scs edge caller before queries index output receipt consumerIndex trace
      exact SelectedInvocationAt.rec
          (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ trace => ChildCovered checkEmpty r n p h k edgesOf trace)
          (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ trace => TupleCovered checkEmpty r n p h k edgesOf trace)
          (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ trace => SelectedCovered checkEmpty r n p h k edgesOf trace)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace

theorem eager_selected_output_event_ledger
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
      ∃ (earlier later : List Output),
        outputs (SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf)
          consume scs edge caller before queries) = earlier ++ outputs (consume receipt) ++ later ∧
        (outputs (consume receipt))[consumerIndex]? = some output ∧
        index = earlier.length + consumerIndex
 := by
  obtain ⟨receipt, consumerIndex, trace, earlier, later, whole, found, offset⟩ :=
    SourcePruningEnumerationSharedInvocationTrace.selected_invocation_origin
      checkEmpty r n p h k edgesOf .eager
      (SourcePruningEnumerationSharedInvocationTrace.eager_invocation_at checkEmpty r n p h k edgesOf)
      consume scs edge caller before queries index output observed
  obtain ⟨events, ledger⟩ :=
    (invocation_event_ledgers checkEmpty r n p h k edgesOf).2.2
      .eager consume scs edge caller before queries index output receipt consumerIndex trace []
  exact ⟨receipt, consumerIndex, events, ledger, earlier, later, whole, found, offset⟩

end MicroCFTA.SourcePruningEnumerationInvocationEventLedger
