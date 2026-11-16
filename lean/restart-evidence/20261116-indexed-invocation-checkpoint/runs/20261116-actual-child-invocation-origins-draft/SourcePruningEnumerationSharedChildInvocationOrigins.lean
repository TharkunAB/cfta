import MicroCFTA.SourcePruningEnumerationSharedInvocationCombinators

namespace MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs scan_output_block_origin)
open SourcePruningEnumerationSharedCallbackOutputBlocks (consume_selected_output_block_origin)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Done" => Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "Stopped" => Observation width → Option Cached → Result Output Reason width
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

theorem shallow_invocation_at
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (incoming : Node) (scs : List Suspended) (caller : Caller width)
    (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
    (index : Nat) (output : Output)
    (observed : (outputs (runPolicy checkEmpty r n p h k edgesOf .shallow
      scs incoming caller before queries done stopped))[index]? = some output) :
    ∃ (exit : ChildExit width) (localIndex : Nat),
      ChildInvocationAt checkEmpty r n p h k edgesOf .shallow
        scs incoming caller before queries done stopped index output exit localIndex ∧
      ∃ (earlier later : List Output),
        outputs (runPolicy checkEmpty r n p h k edgesOf .shallow
          scs incoming caller before queries done stopped) =
            earlier ++ childExitOutputs done stopped exit ++ later ∧
        (childExitOutputs done stopped exit)[localIndex]? = some output ∧
        index = earlier.length + localIndex := by
  have stoppedCase (observation : Observation width) (candidate : Option Cached)
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        (observation, candidate)) (shape : ShallowStopped observation candidate)
      (route : runPolicy checkEmpty r n p h k edgesOf .shallow
        scs incoming caller before queries done stopped = stopped observation candidate) :
      ∃ (exit : ChildExit width) (localIndex : Nat),
        ChildInvocationAt checkEmpty r n p h k edgesOf .shallow
          scs incoming caller before queries done stopped index output exit localIndex ∧
        ∃ (earlier later : List Output),
          outputs (runPolicy checkEmpty r n p h k edgesOf .shallow
            scs incoming caller before queries done stopped) =
              earlier ++ childExitOutputs done stopped exit ++ later ∧
          (childExitOutputs done stopped exit)[localIndex]? = some output ∧
          index = earlier.length + localIndex := by
    have found : (outputs (stopped observation candidate))[index]? = some output := by
      rw [route] at observed
      exact observed
    refine ⟨.stopped observation candidate, index,
      .shallow_stopped actual shape found, [], [], ?_, found, by simp⟩
    simpa only [List.nil_append, List.append_nil, childExitOutputs] using congrArg outputs route
  cases actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries with
  | mk observation candidate =>
      rcases observation with ⟨raw, reached, saved, outer, waiting⟩
      cases raw with
      | error fault =>
          apply stoppedCase _ _ actual (by trivial)
          simp only [runPolicy, shallowVisit, actual]
      | ok possible =>
          cases possible with
          | none =>
              apply stoppedCase _ _ actual (by trivial)
              simp only [runPolicy, shallowVisit, actual]
          | some results =>
              cases results with
              | nil =>
                  apply stoppedCase _ _ actual (by trivial)
                  simp only [runPolicy, shallowVisit, actual]
              | cons first rest =>
                  cases first with
                  | error fault =>
                      apply stoppedCase _ _ actual (by trivial)
                      simp only [runPolicy, shallowVisit, actual]
                  | ok payload =>
                      rcases payload with ⟨fragment, returned⟩
                      cases rest with
                      | cons second tail =>
                          apply stoppedCase _ _ actual (by trivial)
                          simp only [runPolicy, shallowVisit, actual]
                      | nil =>
                          cases candidate with
                          | none =>
                              apply stoppedCase _ _ actual (by trivial)
                              simp only [runPolicy, shallowVisit, actual]
                          | some after =>
                              have found : (outputs (done fragment reached saved after))[index]? = some output := by
                                simpa only [runPolicy, shallowVisit, actual] using observed
                              refine ⟨.done fragment reached saved after, index,
                                .shallow_done actual found, [], [], ?_, found, by simp⟩
                              simp only [runPolicy, shallowVisit, actual, childExitOutputs,
                                List.nil_append, List.append_nil]

theorem eager_invocation_at
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (incoming : Node) (scs : List Suspended) (caller : Caller width)
    (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
    (index : Nat) (output : Output)
    (observed : (outputs (runPolicy checkEmpty r n p h k edgesOf .eager
      scs incoming caller before queries done stopped))[index]? = some output) :
    ∃ (exit : ChildExit width) (localIndex : Nat),
      ChildInvocationAt checkEmpty r n p h k edgesOf .eager
        scs incoming caller before queries done stopped index output exit localIndex ∧
      ∃ (earlier later : List Output),
        outputs (runPolicy checkEmpty r n p h k edgesOf .eager
          scs incoming caller before queries done stopped) =
            earlier ++ childExitOutputs done stopped exit ++ later ∧
        (childExitOutputs done stopped exit)[localIndex]? = some output ∧
        index = earlier.length + localIndex := by
  have allHeights : ∀ bound, ∀ (value : Node), MergedOrdinaryHeight.height value = bound →
      ∀ (bucket : List Suspended) (current : Caller width) (cache : Cached) (savedQueries : Queries)
        (yes : Done) (no : Stopped) (position : Nat) (result : Output),
      (outputs (runPolicy checkEmpty r n p h k edgesOf .eager
        bucket value current cache savedQueries yes no))[position]? = some result →
      ∃ (exit : ChildExit width) (localIndex : Nat),
        ChildInvocationAt checkEmpty r n p h k edgesOf .eager
          bucket value current cache savedQueries yes no position result exit localIndex ∧
        ∃ (earlier later : List Output),
          outputs (runPolicy checkEmpty r n p h k edgesOf .eager
            bucket value current cache savedQueries yes no) =
              earlier ++ childExitOutputs yes no exit ++ later ∧
          (childExitOutputs yes no exit)[localIndex]? = some result ∧
          position = earlier.length + localIndex := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro value heightSame bucket current cache savedQueries yes no position result found
        cases ordinary : ordinaryNonterminal bucket value with
        | false =>
            have route : runPolicy checkEmpty r n p h k edgesOf .eager
                bucket value current cache savedQueries yes no =
                runPolicy checkEmpty r n p h k edgesOf .shallow
                  bucket value current cache savedQueries yes no :=
              SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback
                checkEmpty r n p h k edgesOf bucket value current cache savedQueries yes no ordinary
            have shallowFound := found
            rw [route] at shallowFound
            obtain ⟨exit, localIndex, trace, earlier, later, whole, callbackFound, offset⟩ :=
              shallow_invocation_at checkEmpty r n p h k edgesOf value bucket current cache
                savedQueries yes no position result shallowFound
            refine ⟨exit, localIndex, .eager_fallback ordinary trace,
              earlier, later, ?_, callbackFound, offset⟩
            rw [route]
            exact whole
        | true =>
            have childIH : ∀ (candidate : Node) (childBucket : List Suspended) (childCaller : Caller width)
                (childBefore : Cached) (childQueries : Queries) (doneChild : Done) (stopChild : Stopped)
                (childIndex : Nat) (childOutput : Output),
              (outputs (runPolicy checkEmpty r n p h k edgesOf (.guarded value)
                childBucket candidate childCaller childBefore childQueries doneChild stopChild))[childIndex]? = some childOutput →
              ∃ (exit : ChildExit width) (localIndex : Nat),
                ChildInvocationAt checkEmpty r n p h k edgesOf (.guarded value)
                  childBucket candidate childCaller childBefore childQueries doneChild stopChild
                  childIndex childOutput exit localIndex ∧
                ∃ (earlier later : List Output),
                  outputs (runPolicy checkEmpty r n p h k edgesOf (.guarded value)
                    childBucket candidate childCaller childBefore childQueries doneChild stopChild) =
                      earlier ++ childExitOutputs doneChild stopChild exit ++ later ∧
                  (childExitOutputs doneChild stopChild exit)[localIndex]? = some childOutput ∧
                  childIndex = earlier.length + localIndex := by
              intro candidate childBucket childCaller childBefore childQueries doneChild stopChild childIndex childOutput childFound
              by_cases lower : MergedOrdinaryHeight.height candidate < MergedOrdinaryHeight.height value
              · have smaller : MergedOrdinaryHeight.height candidate < bound := by
                  rw [← heightSame]
                  exact lower
                have eagerFound : (outputs (runPolicy checkEmpty r n p h k edgesOf .eager
                    childBucket candidate childCaller childBefore childQueries doneChild stopChild))[childIndex]? =
                      some childOutput := by
                  simpa only [runPolicy, dite_eq_left lower] using childFound
                obtain ⟨exit, localIndex, trace, earlier, later, whole, callbackFound, offset⟩ :=
                  ih (MergedOrdinaryHeight.height candidate) smaller candidate rfl childBucket childCaller
                    childBefore childQueries doneChild stopChild childIndex childOutput eagerFound
                refine ⟨exit, localIndex, .guarded_lower lower trace,
                  earlier, later, ?_, callbackFound, offset⟩
                simpa only [runPolicy, dite_eq_left lower] using whole
              · have shallowFound : (outputs (runPolicy checkEmpty r n p h k edgesOf .shallow
                    childBucket candidate childCaller childBefore childQueries doneChild stopChild))[childIndex]? =
                      some childOutput := by
                  simpa only [runPolicy, dite_eq_right lower] using childFound
                obtain ⟨exit, localIndex, trace, earlier, later, whole, callbackFound, offset⟩ :=
                  shallow_invocation_at checkEmpty r n p h k edgesOf candidate childBucket childCaller
                    childBefore childQueries doneChild stopChild childIndex childOutput shallowFound
                refine ⟨exit, localIndex, .guarded_else lower trace,
                  earlier, later, ?_, callbackFound, offset⟩
                simpa only [runPolicy, dite_eq_right lower] using whole
            let visit := fun edge reached retained captured =>
              visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded value))
                (consumeSelected yes reached retained) bucket edge reached captured retained
            have route : runPolicy checkEmpty r n p h k edgesOf .eager
                bucket value current cache savedQueries yes no =
                scan visit cache (edgesOf value) current savedQueries :=
              SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary
                checkEmpty r n p h k edgesOf bucket value current cache savedQueries yes no ordinary
            have scanFound := found
            rw [route] at scanFound
            obtain ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier,
              rowResult, rowIndex, later, order, past, rowRun, rowFound, offset, decomposition⟩ :=
              scan_output_block_origin visit cache (edgesOf value) current savedQueries position result scanFound
            have selectedFound : (outputs (visitSelected
                (runPolicy checkEmpty r n p h k edgesOf (.guarded value))
                (consumeSelected yes rowCaller rowQueries) bucket edge rowCaller cache rowQueries))[rowIndex]? =
                  some result := by
              change (outputs (visit edge rowCaller rowQueries cache))[rowIndex]? = some result
              rw [rowRun]
              exact rowFound
            obtain ⟨receipt, consumerIndex, selectedTrace, receiptEarlier, receiptLater,
              selectedWhole, receiptFound, receiptOffset⟩ :=
              selected_invocation_origin checkEmpty r n p h k edgesOf (.guarded value) childIH
                (consumeSelected yes rowCaller rowQueries) bucket edge rowCaller cache rowQueries
                rowIndex result selectedFound
            obtain ⟨fragment, reached, retained, after, receiptSame, _block⟩ :=
              consume_selected_output_block_origin yes rowCaller rowQueries receipt consumerIndex result receiptFound
            subst receipt
            have consumeOutputs : outputs (consumeSelected yes rowCaller rowQueries
                (.complete fragment reached retained after)) = outputs (yes fragment reached retained after) := by
              simp only [consumeSelected]
              cases yes fragment reached retained after <;> rfl
            rw [consumeOutputs] at receiptFound selectedWhole
            have rowWhole : outputs rowResult =
                receiptEarlier ++ outputs (yes fragment reached retained after) ++ receiptLater := by
              rw [← rowRun]
              exact selectedWhole
            refine ⟨.done fragment reached retained after, consumerIndex,
              .eager_ordinary ordinary order past rowRun selectedTrace offset receiptFound,
              earlier ++ receiptEarlier, receiptLater ++ later, ?_, receiptFound, ?_⟩
            · rw [route, decomposition, rowWhole]
              simp only [childExitOutputs, List.append_assoc]
            · simp only [List.length_append]
              omega
  exact allHeights (MergedOrdinaryHeight.height incoming) incoming rfl
    scs caller before queries done stopped index output observed

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
