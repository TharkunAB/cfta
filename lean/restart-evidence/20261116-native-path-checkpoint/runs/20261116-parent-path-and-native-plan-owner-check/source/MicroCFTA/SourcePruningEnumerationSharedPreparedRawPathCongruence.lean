import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRawPathCongruence
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
set_option autoImplicit false
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem actual_prepared_child_raw_path_congruence
    (ownCaller childCaller : Caller width) (parentBucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (ownBefore rowOwn : Cached)
    (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare
      ownCaller.checked.native.machine.heap parentBucket edge ownBefore =
      some [((edge.entry.key.symbol, staged, residual), rowOwn)])
    (position : Nat) (incoming : Node) (childBucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (indexed : staged[position]? = some (incoming, childBucket, action))
    (valid : ∀ sc ∈ parentBucket, EqualityTrie.Valid sc.trie)
    (childBefore : Cached) (queries : Queries) (checkEmpty : Bool) (r n p h k : Nat)
    (fragment : Fragment) (reached : Caller width) (saved : Queries)
    (read returned : Core) (moved : EnumerationWaitingIndex.Waiting) (after : Option Cached)
    (roots : Nat → Nat) (paths : Roots childBefore.core.representatives roots)
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k childBucket incoming childCaller childBefore queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, read, moved), after)) :
    ∀ (firstIndex secondIndex : Nat) (first second : Suspended),
      parentBucket[firstIndex]? = some first → parentBucket[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie →
      UnionFind.SameClass returned.representatives first.var second.var
 := by
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
        generalize allocated : SourcePruningEnumerationCachedOwn.suspendMany
          ownCaller.checked.native.machine.heap tries ownBefore = allocation at prepared
        cases allocation with
        | none => cases prepared
        | some allocation =>
          rcases allocation with ⟨own, ownAfter⟩
          have rowSame := (List.cons.inj (Option.some.inj prepared)).1
          have stagedSame := congrArg
            (fun row : (Symbol × List Input × Option Constraint) × Cached => row.1.2.1) rowSame
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
          intro sc listed
          rw [← bucketSame]
          exact List.mem_append_left _ listed
    next rejected => cases prepared
  have descendTerminal : ∀ sc ∈ parentBucket,
      [position] ∈ EqualityTrie.fromPathTrie sc.trie →
      ∃ child ∈ childBucket, child.var = sc.var ∧ [] ∈ EqualityTrie.fromPathTrie child.trie := by
    intro sc listed path
    obtain ⟨child, inheritedMember, sameVar, atRoot⟩ :=
      (EqualityTrie.descendScs_exact position parentBucket valid sc.var []).mpr
        ⟨sc, listed, rfl, path⟩
    exact ⟨child, inherited inheritedMember, sameVar, atRoot⟩
  intro firstIndex secondIndex first second firstStored secondStored firstPath secondPath
  obtain ⟨firstChild, firstMember, firstVar, firstRoot⟩ :=
    descendTerminal first (List.mem_of_getElem? firstStored) firstPath
  obtain ⟨secondChild, secondMember, secondVar, secondRoot⟩ :=
    descendTerminal second (List.mem_of_getElem? secondStored) secondPath
  have terminal : childBucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
    apply List.any_eq_true.mpr
    refine ⟨firstChild, firstMember, ?_⟩
    have shape := (EqualityTrie.nil_mem firstChild.trie).mp firstRoot
    simp only [shape, EqualityTrie.isTerminal]
  obtain ⟨_terminalFirst, _rest, _descendants, _recorded, winner, _joined,
      _foldCaller, _foldQueries, _folded, _foldOuter, _partitioned, _processed,
      _foldedCall, _foldEndpoint, _incomingCall, _recordedSame, _joinedValues, _hole,
      _foldedForest, _returnedForest, rawTargets⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_final_raw_target_incidence
      checkEmpty r n p h k childBucket incoming childCaller childBefore queries terminal
      fragment reached saved read returned moved after roots paths actual
  have firstAlias : UnionFind.SameClass returned.representatives winner first.var := by
    have joined := (rawTargets firstChild firstMember firstRoot).2.2.2
    simpa only [firstVar] using joined
  have secondAlias : UnionFind.SameClass returned.representatives winner second.var := by
    have joined := (rawTargets secondChild secondMember secondRoot).2.2.2
    simpa only [secondVar] using joined
  exact UnionFind.sameClass_trans (UnionFind.sameClass_symm firstAlias) secondAlias

end MicroCFTA.SourcePruningEnumerationSharedPreparedRawPathCongruence

#check @MicroCFTA.SourcePruningEnumerationSharedPreparedRawPathCongruence.actual_prepared_child_raw_path_congruence
#print axioms MicroCFTA.SourcePruningEnumerationSharedPreparedRawPathCongruence.actual_prepared_child_raw_path_congruence
