import MicroCFTA.SourcePruningEnumerationSelectedStagedChildInvocation
import MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationOwnAliasForest

namespace MicroCFTA.SourcePruningEnumerationSelectedPathDescent
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
set_option autoImplicit false

/- Note [Original path occurrence at a child invocation]
The original occurrence fixes the prefix used to count retained descents.
The successful preparation checks the first path index against the arity.
It therefore supplies the actual staged child at that index.
The selected trace supplies that child's actual invocation and remaining tuple.
The receipt retains the suffix in that child's input bucket.
It does not assert that an unexecuted suffix has been traversed.
-/

private theorem filter_map_indexed {α β : Type}
    (transform : α → β) (keep : β → Bool) (values : List α) (occurrence : Nat) (value : α)
    (found : values[occurrence]? = some value) (retained : keep (transform value) = true) :
    ((values.map transform).filter keep)[((values.take occurrence).map transform |>.filter keep).length]? =
      some (transform value) := by
  induction values generalizing occurrence with
  | nil => simp at found
  | cons first rest ih =>
      cases occurrence with
      | zero =>
          change some first = some value at found
          have same := Option.some.inj found
          subst value
          simp [retained]
      | succ occurrence =>
          change rest[occurrence]? = some value at found
          have later := ih occurrence found
          cases firstKept : keep (transform first) <;> simpa [firstKept] using later

private theorem descend_indexed
    (parentBucket : List Suspended) (occurrence : Nat) (obligation : Suspended)
    (original : parentBucket[occurrence]? = some obligation)
    (valid : EqualityTrie.Valid obligation.trie) (position : Nat) (suffix : List Nat)
    (path : position :: suffix ∈ EqualityTrie.fromPathTrie obligation.trie) :
    (descendScs position parentBucket)[(descendScs position (parentBucket.take occurrence)).length]? =
      some ⟨EqualityTrie.pathTrieDescend obligation.trie position, obligation.var⟩ := by
  have descended := (EqualityTrie.descend_exact obligation.trie valid position suffix).mpr path
  have descendedValid := EqualityTrie.descend_valid obligation.trie valid position
  have retained : (!EqualityTrie.isEmpty (EqualityTrie.pathTrieDescend obligation.trie position)) = true := by
    cases empty : EqualityTrie.isEmpty (EqualityTrie.pathTrieDescend obligation.trie position) with
    | false => rfl
    | true =>
        have noPaths := (EqualityTrie.empty_exact _ descendedValid).mp empty
        rw [noPaths] at descended
        cases descended
  exact filter_map_indexed
    (fun sc : Suspended => (⟨EqualityTrie.pathTrieDescend sc.trie position, sc.var⟩ : Suspended))
    (fun sc : Suspended => !EqualityTrie.isEmpty sc.trie) parentBucket occurrence obligation original retained

private theorem prepared_path_child
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentBucket : List Suspended) (edge : Edge) (before middle : Cached)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare heap parentBucket edge before =
      some [((symbol, staged, residual), middle)])
    (occurrence : Nat) (obligation : Suspended)
    (original : parentBucket[occurrence]? = some obligation)
    (valid : EqualityTrie.Valid obligation.trie) (position : Nat) (suffix : List Nat)
    (path : position :: suffix ∈ EqualityTrie.fromPathTrie obligation.trie) :
    ∃ (incoming : Node) (childBucket : List Suspended)
        (action : Option (EnumerateM Symbol Constraint Fragment)),
      staged[position]? = some (incoming, childBucket, action) ∧
      childBucket[(descendScs position (parentBucket.take occurrence)).length]? =
        some ⟨EqualityTrie.pathTrieDescend obligation.trie position, obligation.var⟩ := by
  have descendantFound := descend_indexed parentBucket occurrence obligation original valid position suffix path
  have inside : (descendScs position (parentBucket.take occurrence)).length <
      (descendScs position parentBucket).length :=
    (List.getElem?_eq_some_iff.mp descendantFound).elim (fun bound _ => bound)
  unfold SourcePruningEnumerationCachedOwn.prepare at prepared
  split at prepared
  next allowed =>
    have childBound : position < edge.children.length :=
      (arityAllows_correct edge.children.length parentBucket).mp allowed obligation
        (List.mem_of_getElem? original) position suffix path
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
            obtain ⟨incoming, childStored⟩ : ∃ incoming, edge.children[position]? = some incoming :=
              ⟨edge.children[position], List.getElem?_eq_getElem childBound⟩
            have zipped : edge.children.zipIdx[position]? = some (incoming, position) := by
              simp only [List.getElem?_zipIdx, childStored, Option.map_some, Nat.zero_add]
            refine ⟨incoming, descendScs position parentBucket ++ descendScs position own,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs position parentBucket ++ descendScs position own) incoming, ?_, ?_⟩
            · simp only [← stagedSame, List.getElem?_map, zipped, Option.map_some]
            · rw [List.getElem?_append_left inside]
              exact descendantFound
  next rejected => cases prepared

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem selected_original_path_child_invocation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (parentBucket : List Suspended) (edge : Edge) (caller finalCaller : Caller width)
    (before middle finished : Cached) (queries finalQueries : Queries)
    (index : Nat) (output : Output) (fragment : Fragment) (consumerIndex : Nat)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap parentBucket edge before =
      some [((symbol, staged, residual), middle)])
    (occurrence : Nat) (obligation : Suspended)
    (original : parentBucket[occurrence]? = some obligation)
    (valid : EqualityTrie.Valid obligation.trie) (position : Nat) (suffix : List Nat)
    (path : position :: suffix ∈ EqualityTrie.fromPathTrie obligation.trie)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume parentBucket edge caller before queries
      index output (.complete fragment finalCaller finalQueries finished) consumerIndex) :
    let tupleDone : TupleDone := fun produced current capturedQueries captured =>
      consume (.complete (.node symbol produced) current capturedQueries
        (SelectedEdge.finish residual (.node symbol produced) captured))
    let tupleStopped : TupleStopped := fun completed observation candidate =>
      consume (.stopped completed observation candidate)
    let descendant : Suspended := ⟨EqualityTrie.pathTrieDescend obligation.trie position, obligation.var⟩
    ∃ (incoming : Node) (childBucket : List Suspended)
        (action : Option (EnumerateM Symbol Constraint Fragment))
        (priorStaged laterStaged : List Input) (priorFragments : List Fragment)
        (childCaller : Caller width) (childBefore : Cached) (childQueries : Queries)
        (childRootIndex : Nat) (childFragment : Fragment) (reached : Caller width)
        (saved : Queries) (after : Cached) (childCallbackIndex : Nat)
        (remainingFragments : List Fragment) (afterChildren : Cached),
      staged[position]? = some (incoming, childBucket, action) ∧
      staged = priorStaged ++ (incoming, childBucket, action) :: laterStaged ∧
      priorStaged.length = position ∧ priorFragments.length = position ∧
      childBucket[(descendScs position (parentBucket.take occurrence)).length]? = some descendant ∧
      EqualityTrie.Valid descendant.trie ∧ suffix ∈ EqualityTrie.fromPathTrie descendant.trie ∧
      fragment = .node symbol (priorFragments ++ childFragment :: remainingFragments) ∧
      finished = SelectedEdge.finish residual fragment afterChildren ∧
      ChildInvocationAt checkEmpty r n p h k edgesOf policy childBucket incoming childCaller childBefore childQueries
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
        childCallbackIndex output (.done remainingFragments finalCaller finalQueries afterChildren) consumerIndex ∧
      ∀ left right, UnionFind.SameClass after.core.representatives left right →
        UnionFind.SameClass finished.core.representatives left right
 := by
  dsimp only
  obtain ⟨incoming, childBucket, action, indexed, descendantFound⟩ :=
    prepared_path_child caller.checked.native.machine.heap parentBucket edge before middle symbol staged residual
      prepared occurrence obligation original valid position suffix path
  have joined := selected_staged_child_invocation checkEmpty r n p h k edgesOf policy consume
    parentBucket edge caller before queries index output fragment finalCaller finalQueries finished consumerIndex
    symbol staged residual middle prepared position incoming childBucket action indexed trace
  dsimp only at joined
  obtain ⟨priorStaged, laterStaged, priorFragments, childCaller, childBefore, childQueries,
    childRootIndex, childFragment, reached, saved, after, childCallbackIndex, remainingFragments,
    afterChildren, split, priorLength, completedLength, assembled, finishedEq, child, tail⟩ := joined
  let tupleDone : TupleDone := fun produced current capturedQueries captured =>
    consume (.complete (.node symbol produced) current capturedQueries
      (SelectedEdge.finish residual (.node symbol produced) captured))
  let tupleStopped : TupleStopped := fun completed observation candidate =>
    consume (.stopped completed observation candidate)
  have tailAliases := SourcePruningEnumerationInvocationRawAliasGrowth.children_done_sameClass_forward
    (checkEmpty := checkEmpty) (r := r) (n := n) (p := p) (h := h) (k := k) (edgesOf := edgesOf) (policy := policy)
    (done := fun remaining => tupleDone (priorFragments ++ childFragment :: remaining))
    (stopped := fun completed => tupleStopped (priorFragments ++ childFragment :: completed))
    (inputs := laterStaged.map (fun input => (input.1, input.2.1)))
    (caller := reached) (reached := finalCaller) (before := after) (after := afterChildren)
    (queries := saved) (saved := finalQueries) (index := childCallbackIndex) (output := output)
    (fragments := remainingFragments) (localIndex := consumerIndex) (trace := tail)
  have finalForest : finished.core.representatives = afterChildren.core.representatives := by
    rw [finishedEq]
    exact SourcePruningEnumerationOwnAliasForest.finish_forest residual fragment afterChildren
  refine ⟨incoming, childBucket, action, priorStaged, laterStaged, priorFragments,
    childCaller, childBefore, childQueries, childRootIndex, childFragment, reached, saved,
    after, childCallbackIndex, remainingFragments, afterChildren, indexed, split, priorLength,
    completedLength, descendantFound, EqualityTrie.descend_valid obligation.trie valid position,
    (EqualityTrie.descend_exact obligation.trie valid position suffix).mpr path,
    assembled, finishedEq, child, tail, ?_⟩
  intro left right same
  rw [finalForest]
  exact tailAliases left right same

end MicroCFTA.SourcePruningEnumerationSelectedPathDescent

#check @MicroCFTA.SourcePruningEnumerationSelectedPathDescent.selected_original_path_child_invocation
#print axioms MicroCFTA.SourcePruningEnumerationSelectedPathDescent.selected_original_path_child_invocation
