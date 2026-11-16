import MicroCFTA.SourcePruningEnumerationStagedChildInvocation

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

private theorem indexed_split {α : Type u} (values : List α) (position : Nat) (value : α)
    (found : values[position]? = some value) :
    ∃ (prior later : List α), values = prior ++ value :: later ∧ prior.length = position := by
  induction values generalizing position with
  | nil =>
      simp at found
  | cons first rest ih =>
      cases position with
      | zero =>
          change some first = some value at found
          have same : first = value := Option.some.inj found
          subst value
          exact ⟨[], rest, rfl, rfl⟩
      | succ position =>
          change rest[position]? = some value at found
          obtain ⟨prior, later, split, priorLength⟩ := ih position found
          refine ⟨first :: prior, later, ?_, ?_⟩
          · rw [split]
            rfl
          · simp only [List.length_cons, priorLength]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/- Note [Selected staged child incidence]
The preparation equation fixes the original staged input list.
The indexed lookup fixes one position in that list.
The selected trace supplies the actual tuple trace for that preparation.
The tuple inversion retains the child and tail from the same derivation.
It preserves the output occurrence and both callback indices.
See Note [Staged child invocation position] in
MicroCFTA.SourcePruningEnumerationStagedChildInvocation.
-/

theorem selected_staged_child_invocation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (fragment : Fragment) (finalCaller : Caller width)
    (finalQueries : Queries) (finished : Cached) (consumerIndex : Nat)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint) (middle : Cached)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (indexed : staged[position]? = some (incoming, bucket, action))
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
      index output (.complete fragment finalCaller finalQueries finished) consumerIndex) :
    let tupleDone : TupleDone := fun produced current capturedQueries captured =>
      consume (.complete (.node symbol produced) current capturedQueries
        (SelectedEdge.finish residual (.node symbol produced) captured))
    let tupleStopped : TupleStopped := fun completed observation candidate =>
      consume (.stopped completed observation candidate)
    ∃ (priorStaged laterStaged : List Input) (priorFragments : List Fragment)
        (childCaller : Caller width) (childBefore : Cached) (childQueries : Queries)
        (childRootIndex : Nat) (childFragment : Fragment) (reached : Caller width)
        (saved : Queries) (after : Cached) (childCallbackIndex : Nat)
        (remainingFragments : List Fragment) (afterChildren : Cached),
      staged = priorStaged ++ (incoming, bucket, action) :: laterStaged ∧
      priorStaged.length = position ∧ priorFragments.length = position ∧
      fragment = .node symbol (priorFragments ++ childFragment :: remainingFragments) ∧
      finished = SelectedEdge.finish residual fragment afterChildren ∧
      ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming childCaller childBefore childQueries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun remaining => tupleDone (priorFragments ++ produced :: remaining))
            (fun completed => tupleStopped (priorFragments ++ produced :: completed))
            (laterStaged.map (fun input => (input.1, input.2.1))) current captured capturedQueries)
        (fun observation candidate => tupleStopped priorFragments observation candidate)
        childRootIndex output (.done childFragment reached saved after) childCallbackIndex ∧
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun remaining => tupleDone (priorFragments ++ childFragment :: remaining))
        (fun completed => tupleStopped (priorFragments ++ childFragment :: completed))
        (laterStaged.map (fun input => (input.1, input.2.1))) reached after saved
        childCallbackIndex output (.done remainingFragments finalCaller finalQueries afterChildren) consumerIndex := by
  dsimp only
  obtain ⟨chosenSymbol, chosenStaged, chosenResidual, chosenMiddle,
      fragments, afterChildren, actual, children, assembled, finishedEq⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf policy consume scs edge
      caller before queries index output fragment finalCaller finalQueries finished consumerIndex trace
  have rowSame : ((chosenSymbol, chosenStaged, chosenResidual), chosenMiddle) =
      ((symbol, staged, residual), middle) :=
    (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
  have symbolSame : chosenSymbol = symbol :=
    congrArg (fun row : Row => row.1.1) rowSame
  have stagedSame : chosenStaged = staged :=
    congrArg (fun row : Row => row.1.2.1) rowSame
  have residualSame : chosenResidual = residual :=
    congrArg (fun row : Row => row.1.2.2) rowSame
  have middleSame : chosenMiddle = middle :=
    congrArg (fun row : Row => row.2) rowSame
  subst chosenSymbol chosenStaged chosenResidual chosenMiddle
  obtain ⟨priorStaged, laterStaged, split, priorLength⟩ :=
    indexed_split staged position (incoming, bucket, action) indexed
  have inputSplit : staged.map (fun input => (input.1, input.2.1)) =
      priorStaged.map (fun input => (input.1, input.2.1)) ++
        (incoming, bucket) :: laterStaged.map (fun input => (input.1, input.2.1)) := by
    rw [split, List.map_append, List.map_cons]
  rw [inputSplit] at children
  let tupleDone : TupleDone := fun produced current capturedQueries captured =>
    consume (.complete (.node symbol produced) current capturedQueries
      (SelectedEdge.finish residual (.node symbol produced) captured))
  let tupleStopped : TupleStopped := fun completed observation candidate =>
    consume (.stopped completed observation candidate)
  obtain ⟨priorFragments, childCaller, childBefore, childQueries, childRootIndex,
      childFragment, reached, saved, after, childCallbackIndex, remainingFragments,
      completedLength, fragmentShape, child, tail⟩ :=
    children_done_prefix_invocation checkEmpty r n p h k edgesOf policy tupleDone tupleStopped
      (priorStaged.map (fun input => (input.1, input.2.1))) incoming bucket
      (laterStaged.map (fun input => (input.1, input.2.1))) caller middle queries index output
      fragments finalCaller finalQueries afterChildren consumerIndex children
  have samePosition : priorFragments.length = position := by
    have stagedLength : priorFragments.length = priorStaged.length := by
      simpa only [List.length_map] using completedLength
    exact stagedLength.trans priorLength
  rw [fragmentShape] at assembled
  exact ⟨priorStaged, laterStaged, priorFragments, childCaller, childBefore, childQueries,
    childRootIndex, childFragment, reached, saved, after, childCallbackIndex,
    remainingFragments, afterChildren, split, priorLength, samePosition,
    assembled, finishedEq, child, tail⟩

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

#check @MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.selected_staged_child_invocation
#print axioms MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.selected_staged_child_invocation
