import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

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

/- See Note [Indexed invocation ancestry] in
MicroCFTA.SourcePruningEnumerationSharedInvocationTrace. -/
theorem children_invocation_origin
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (childIH : ∀ (incoming : Node) (scs : List Suspended) (caller : Caller width)
        (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
        (index : Nat) (output : Output),
      (outputs (runPolicy checkEmpty r n p h k edgesOf policy
        scs incoming caller before queries done stopped))[index]? = some output →
      ∃ (exit : ChildExit width) (localIndex : Nat),
        ChildInvocationAt checkEmpty r n p h k edgesOf policy
          scs incoming caller before queries done stopped index output exit localIndex ∧
        ∃ (earlier later : List Output),
          outputs (runPolicy checkEmpty r n p h k edgesOf policy
            scs incoming caller before queries done stopped) =
              earlier ++ childExitOutputs done stopped exit ++ later ∧
          (childExitOutputs done stopped exit)[localIndex]? = some output ∧
          index = earlier.length + localIndex)
    (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries) (index : Nat) (output : Output)
    (observed : (outputs (visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
      done stopped inputs caller before queries))[index]? = some output) :
    ∃ (exit : TupleExit width) (localIndex : Nat),
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        done stopped inputs caller before queries index output exit localIndex ∧
      ∃ (earlier later : List Output),
        outputs (visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
          done stopped inputs caller before queries) =
            earlier ++ tupleExitOutputs done stopped exit ++ later ∧
        (tupleExitOutputs done stopped exit)[localIndex]? = some output ∧
        index = earlier.length + localIndex := by
  induction inputs generalizing caller before queries done stopped index with
  | nil =>
      refine ⟨.done [] caller queries before, index, .nil observed, [], [], ?_, observed, ?_⟩
      · simp only [visitChildren, tupleExitOutputs, List.nil_append, List.append_nil]
      · simp
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      let visit := runPolicy (width := width) (Output := Output) (Reason := Reason) checkEmpty r n p h k edgesOf policy
      let yes := fun fragment reached saved after =>
        visitChildren visit (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved
      let no := fun observation candidate => stopped [] observation candidate
      obtain ⟨exit, childIndex, childTrace, earlier, later, decomposition, found, offset⟩ :=
        childIH incoming bucket caller before queries yes no index output
          (by simpa only [visitChildren, visit, yes, no] using observed)
      cases exit with
      | done fragment reached saved after =>
          change (outputs (visitChildren visit (fun fragments => done (fragment :: fragments))
            (fun completed => stopped (fragment :: completed)) rest reached after saved))[childIndex]? =
              some output at found
          obtain ⟨tailExit, localIndex, tailTrace, prior, suffix,
              tailDecomposition, terminalFound, tailOffset⟩ :=
            ih (done := fun fragments => done (fragment :: fragments))
              (stopped := fun completed => stopped (fragment :: completed))
              (caller := reached) (before := after) (queries := saved) (index := childIndex) found
          have callbackSame : tupleExitOutputs (fun fragments => done (fragment :: fragments))
              (fun completed => stopped (fragment :: completed)) tailExit =
              tupleExitOutputs done stopped (TupleExit.prepend fragment tailExit) := by
            cases tailExit <;> rfl
          refine ⟨TupleExit.prepend fragment tailExit, localIndex,
            .cons_done childTrace tailTrace, earlier ++ prior, suffix ++ later, ?_, ?_, ?_⟩
          · change outputs (visit bucket incoming caller before queries yes no) = _
            rw [decomposition]
            change earlier ++ outputs (visitChildren visit (fun fragments => done (fragment :: fragments))
              (fun completed => stopped (fragment :: completed)) rest reached after saved) ++ later = _
            rw [tailDecomposition, callbackSame]
            simp only [List.append_assoc]
          · rw [← callbackSame]
            exact terminalFound
          · simp only [List.length_append]
            omega
      | stopped observation candidate =>
          exact ⟨.stopped [] observation candidate, childIndex, .cons_stopped childTrace,
            earlier, later, decomposition, found, offset⟩

theorem selected_invocation_origin
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (childIH : ∀ (incoming : Node) (scs : List Suspended) (caller : Caller width)
        (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
        (index : Nat) (output : Output),
      (outputs (runPolicy checkEmpty r n p h k edgesOf policy
        scs incoming caller before queries done stopped))[index]? = some output →
      ∃ (exit : ChildExit width) (localIndex : Nat),
        ChildInvocationAt checkEmpty r n p h k edgesOf policy
          scs incoming caller before queries done stopped index output exit localIndex ∧
        ∃ (earlier later : List Output),
          outputs (runPolicy checkEmpty r n p h k edgesOf policy
            scs incoming caller before queries done stopped) =
              earlier ++ childExitOutputs done stopped exit ++ later ∧
          (childExitOutputs done stopped exit)[localIndex]? = some output ∧
          index = earlier.length + localIndex)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (visitSelected (runPolicy checkEmpty r n p h k edgesOf policy)
      consume scs edge caller before queries))[index]? = some output) :
    ∃ (receipt : Receipt width) (consumerIndex : Nat),
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output receipt consumerIndex ∧
      ∃ (earlier later : List Output),
        outputs (visitSelected (runPolicy checkEmpty r n p h k edgesOf policy)
          consume scs edge caller before queries) = earlier ++ outputs (consume receipt) ++ later ∧
        (outputs (consume receipt))[consumerIndex]? = some output ∧
        index = earlier.length + consumerIndex := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none =>
      simp only [visitSelected, prepared] at observed ⊢
      exact ⟨.unhandled, index, .unhandled_none prepared observed, [], [], by simp, observed, by simp⟩
  | some rows =>
      cases rows with
      | nil =>
          simp only [visitSelected, prepared] at observed ⊢
          exact ⟨.rejected caller queries before, index, .rejected prepared observed,
            [], [], by simp, observed, by simp⟩
      | cons row rest =>
          cases rest with
          | cons second tail =>
              simp only [visitSelected, prepared] at observed ⊢
              exact ⟨.unhandled, index, .unhandled_many prepared observed,
                [], [], by simp, observed, by simp⟩
          | nil =>
              rcases row with ⟨⟨symbol, staged, residual⟩, middle⟩
              simp only [visitSelected, prepared] at observed ⊢
              obtain ⟨exit, localIndex, children, earlier, later, decomposition, found, offset⟩ :=
                children_invocation_origin checkEmpty r n p h k edgesOf policy childIH
                  (fun fragments reached saved after => consume (.complete (.node symbol fragments)
                    reached saved (SelectedEdge.finish residual (.node symbol fragments) after)))
                  (fun completed observation candidate => consume (.stopped completed observation candidate))
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries index output observed
              cases exit with
              | done fragments reached saved after =>
                  exact ⟨.complete (.node symbol fragments) reached saved
                    (SelectedEdge.finish residual (.node symbol fragments) after), localIndex,
                    .singleton_done prepared children, earlier, later, decomposition, found, offset⟩
              | stopped completed observation candidate =>
                  exact ⟨.stopped completed observation candidate, localIndex,
                    .singleton_stopped prepared children, earlier, later, decomposition, found, offset⟩

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
