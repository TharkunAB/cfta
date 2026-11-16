import MicroCFTA.SourcePruningEnumerationStagedChildRoots
import MicroCFTA.SourcePruningEnumerationSharedPreparedRawPathCongruence
import MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationOwnAliasForest

namespace MicroCFTA.SourcePruningEnumerationSelectedChildPathAliases
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
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
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v w
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → ChildDispatch.Observation width → Option Cached → Result Output Reason width
set_option autoImplicit false

/- Note [Selected child path aliases]
The selected trace identifies one actual preparation and tuple.
The indexed list split fixes the original staged child position.
The joint prefix receipt supplies roots for that same child entry.
The first original path makes that child's bucket terminal.
The actual dispatch derives both raw aliases at its returned Core.
The same tuple tail transports those aliases to the selected return.
Residual finish retains the forest.

The pure descent proof below reuses the checked prefix of
actual_prepared_child_raw_path_congruence.
No output equality, fresh roots, future alias relation or model is assumed.
This theorem proves raw aliases only.
-/

private theorem split_indexed {α : Type w} (values : List α) (position : Nat) (value : α)
    (indexed : values[position]? = some value) :
    ∃ (prior rest : List α), values = prior ++ value :: rest ∧ prior.length = position := by
  induction values generalizing position with
  | nil => cases position <;> cases indexed
  | cons first tail ih =>
      cases position with
      | zero =>
          change some first = some value at indexed
          have same := Option.some.inj indexed
          subst value
          exact ⟨[], tail, rfl, rfl⟩
      | succ position =>
          have tailIndexed : tail[position]? = some value := indexed
          obtain ⟨prior, rest, split, length⟩ := ih position tailIndexed
          refine ⟨first :: prior, rest, ?_, ?_⟩
          · rw [split]
            rfl
          · exact congrArg Nat.succ length

private theorem prepared_child_terminal
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentBucket : List Suspended) (edge : Edge) (before middle : Cached)
    (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare heap parentBucket edge before =
      some [((edge.entry.key.symbol, staged, residual), middle)])
    (position : Nat) (incoming : Node) (childBucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (indexed : staged[position]? = some (incoming, childBucket, action))
    (valid : ∀ sc ∈ parentBucket, EqualityTrie.Valid sc.trie)
    (original : Suspended) (listed : original ∈ parentBucket)
    (path : [position] ∈ EqualityTrie.fromPathTrie original.trie) :
    childBucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
  have inherited : descendScs position parentBucket ⊆ childBucket := by
    unfold SourcePruningEnumerationCachedOwn.prepare at prepared
    split at prepared
    next allowed =>
      generalize projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = plan at prepared
      cases plan with
      | none => cases prepared
      | some plan =>
          rcases plan with ⟨tries, kept⟩
          dsimp only at prepared
          generalize allocated : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = allocation at prepared
          cases allocation with
          | none => cases prepared
          | some allocation =>
              rcases allocation with ⟨own, ownAfter⟩
              have rowSame := (List.cons.inj (Option.some.inj prepared)).1
              have stagedSame := congrArg (fun row : Row => row.1.2.1) rowSame
              dsimp only at stagedSame
              rw [← stagedSame, List.getElem?_map] at indexed
              obtain ⟨indexedChild, indexedStored, inputSame⟩ := Option.map_eq_some_iff.mp indexed
              have indexSame : indexedChild.2 = position := by
                rw [List.getElem?_zipIdx] at indexedStored
                obtain ⟨storedChild, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
                simp
              have bucketSame : descendScs indexedChild.2 parentBucket ++
                  descendScs indexedChild.2 own = childBucket :=
                congrArg (fun input : Input => input.2.1) inputSame
              rw [indexSame] at bucketSame
              intro sc member
              rw [← bucketSame]
              exact List.mem_append_left _ member
    next rejected => cases prepared
  obtain ⟨child, inheritedMember, _sameVar, atRoot⟩ :=
    (EqualityTrie.descendScs_exact position parentBucket valid original.var []).mpr
      ⟨original, listed, rfl, path⟩
  have childMember := inherited inheritedMember
  apply List.any_eq_true.mpr
  refine ⟨child, childMember, ?_⟩
  have shape := (EqualityTrie.nil_mem child.trie).mp atRoot
  simp only [shape, EqualityTrie.isTerminal]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original same-position trie occurrences remain aliased at the actual selected return. -/
theorem selected_child_path_sameClass
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (parentBucket : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before middle after : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap
      parentBucket edge before = some [((edge.entry.key.symbol, staged, residual), middle)])
    (total : UnionFind.Total before.core.representatives)
    (valid : ∀ sc ∈ parentBucket, EqualityTrie.Valid sc.trie)
    (position : Nat) (incoming : Node) (childBucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (indexed : staged[position]? = some (incoming, childBucket, action))
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy
      consume parentBucket edge caller before queries index output
        (.complete fragment reached saved after) consumerIndex) :
    ∀ (firstIndex secondIndex : Nat) (first second : Suspended),
      parentBucket[firstIndex]? = some first → parentBucket[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie →
      UnionFind.SameClass after.core.representatives first.var second.var := by
  obtain ⟨actualSymbol, actualStaged, actualResidual, actualMiddle, fragments, afterChildren,
    own, children, _fragmentShape, finishEq⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf policy consume parentBucket edge
      caller before queries index output fragment reached saved after consumerIndex trace
  have rowSame : ((actualSymbol, actualStaged, actualResidual), actualMiddle) =
      ((edge.entry.key.symbol, staged, residual), middle) :=
    (List.cons.inj (Option.some.inj (own.symm.trans prepared))).1
  have symbolSame := congrArg (fun row : Row => row.1.1) rowSame
  have stagedSame := congrArg (fun row : Row => row.1.2.1) rowSame
  have residualSame := congrArg (fun row : Row => row.1.2.2) rowSame
  have middleSame := congrArg (fun row : Row => row.2) rowSame
  dsimp only at symbolSame stagedSame residualSame middleSame
  subst actualSymbol actualStaged actualResidual actualMiddle
  obtain ⟨prior, remaining, split, _priorLength⟩ :=
    split_indexed staged position (incoming, childBucket, action) indexed
  let priorInputs := prior.map (fun input : Input => (input.1, input.2.1))
  let remainingInputs := remaining.map (fun input : Input => (input.1, input.2.1))
  have inputSplit : staged.map (fun input => (input.1, input.2.1)) =
      priorInputs ++ (incoming, childBucket) :: remainingInputs := by
    simpa only [List.map_append, List.map_cons] using
      congrArg (List.map (fun input : Input => (input.1, input.2.1))) split
  let doneTuple : TupleDone := fun produced current capturedQueries captured =>
    consume (.complete (.node edge.entry.key.symbol produced) current capturedQueries
      (SelectedEdge.finish residual (.node edge.entry.key.symbol produced) captured))
  let stoppedTuple : TupleStopped := fun completed observation candidate =>
    consume (.stopped completed observation candidate)
  rw [inputSplit] at children
  change ChildrenInvocationAt checkEmpty r n p h k edgesOf policy doneTuple stoppedTuple
    (priorInputs ++ (incoming, childBucket) :: remainingInputs) caller middle queries index output
      (.done fragments reached saved afterChildren) consumerIndex at children
  have middleTotal : UnionFind.Total middle.core.representatives := by
    rw [SourcePruningEnumerationOwnAliasForest.prepare_forest (actual := prepared)]
    exact total
  obtain ⟨priorFragments, childCaller, childBefore, childQueries, childRootIndex,
    childFragment, childReached, childSaved, childAfter, childCallbackIndex, remainingFragments,
    _prefixLength, _fragmentsShape, childTrace, tailTrace, _childTotal, roots, rootPaths⟩ :=
    SourcePruningEnumerationStagedChildRoots.children_done_prefix_invocation_with_roots checkEmpty r n p h k edgesOf policy
      doneTuple stoppedTuple priorInputs incoming childBucket remainingInputs caller middle queries
      index output fragments reached saved afterChildren consumerIndex middleTotal children
  intro firstIndex secondIndex first second firstStored secondStored firstPath secondPath
  have terminal := prepared_child_terminal caller.checked.native.machine.heap parentBucket edge
    before middle staged residual prepared position incoming childBucket action indexed valid
      first (List.mem_of_getElem? firstStored) firstPath
  obtain ⟨returned, read, moved, dispatched, _sameIndex⟩ :=
    terminal_done_dispatch checkEmpty r n p h k edgesOf policy childBucket incoming
      childCaller childBefore childQueries _ _ childRootIndex output childFragment
      childReached childSaved childAfter childCallbackIndex terminal childTrace
  have rawAlias := SourcePruningEnumerationSharedPreparedRawPathCongruence.actual_prepared_child_raw_path_congruence
    caller childCaller parentBucket edge before middle staged residual prepared
    position incoming childBucket action indexed valid childBefore childQueries checkEmpty r n p h k
    childFragment childReached childSaved read returned moved (some childAfter) roots rootPaths dispatched
    firstIndex secondIndex first second firstStored secondStored firstPath secondPath
  have childCore := ChildDispatch.singleton_core checkEmpty r n p h k childBucket incoming
    childCaller childReached childBefore childAfter childQueries childSaved childFragment returned read moved dispatched
  have atChild : UnionFind.SameClass childAfter.core.representatives first.var second.var := by
    rw [childCore]
    exact rawAlias
  have atChildren := SourcePruningEnumerationInvocationRawAliasGrowth.children_done_sameClass_forward
    (trace := tailTrace) first.var second.var atChild
  have finalForest : after.core.representatives = afterChildren.core.representatives := by
    rw [finishEq]
    rfl
  rw [finalForest]
  exact atChildren

end MicroCFTA.SourcePruningEnumerationSelectedChildPathAliases
