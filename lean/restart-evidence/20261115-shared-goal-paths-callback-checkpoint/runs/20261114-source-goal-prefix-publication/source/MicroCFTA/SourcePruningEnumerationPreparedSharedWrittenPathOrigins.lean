import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.SourcePruningEnumerationSharedChildRawTargets
import MicroCFTA.SourcePruningEnumerationSharedIncomingBucketHistory

/-!
# Raw path sources at a prepared shared child write

The actual prepared list fixes the child index and both descended buckets.
The actual shared return supplies the incoming write and the older bucket.
The written list keeps its order and all duplicate occurrences.
Each represented path retains its raw target and its source path.
This result does not preserve obligations through a later recursive clear.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)

set_option autoImplicit false

private theorem descended_occurrence_origin
    (index : Nat) (inputs : List Suspended) (sc : Suspended)
    (member : sc ∈ descendScs index inputs)
    (path : EqualityTrie.Path) (represented : path ∈ EqualityTrie.fromPathTrie sc.trie) :
    ∃ original ∈ inputs,
      sc.var = original.var ∧ index :: path ∈ EqualityTrie.fromPathTrie original.trie := by
  change sc ∈ EqualityTrie.descendScs index inputs at member
  unfold EqualityTrie.descendScs at member
  obtain ⟨mapped, _retained⟩ := List.mem_filter.mp member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp mapped
  cases same
  exact ⟨original, originalMember, rfl,
    SourcePruningEnumerationPathTransport.descended_path_original
      original.trie index path represented⟩

private theorem suspended_occurrence_index
    (start : Nat) (tries : List EqualityTrie.Trie) (sc : Suspended)
    (member : sc ∈ suspendedVars start tries) :
    ∃ (index : Nat) (trie : EqualityTrie.Trie),
      tries[index]? = some trie ∧ sc.var = start + index ∧ sc.trie = trie := by
  induction tries generalizing start with
  | nil => simp only [suspendedVars, List.not_mem_nil] at member
  | cons trie rest ih =>
      change sc ∈ (⟨trie, start⟩ :: suspendedVars (start + 1) rest) at member
      rcases List.mem_cons.mp member with first | later
      · subst sc
        exact ⟨0, trie, rfl, by simp, rfl⟩
      · obtain ⟨index, original, found, varSame, shape⟩ := ih (start + 1) later
        refine ⟨index + 1, original, ?_, ?_, shape⟩
        · simpa only [List.getElem?_cons_succ] using found
        · omega

/-- Each path written by the actual prepared shared child has an indexed raw source. -/
theorem prepared_terminal_child_written_path_origins
    {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentBucket : List Suspended) (edge : EdgeValue Symbol Constraint)
    (captured own : Cached) (symbol : Symbol) (staged : List Child)
    (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare heap parentBucket edge captured =
      some [((symbol, staged, residual), own)])
    (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (selected : staged[position]? = some (incoming, bucket, action))
    (checkEmpty : Bool) (r n p h k : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (read after : Core) (moved : EnumerationWaitingIndex.Waiting) (afterCache : Option Cached)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (actual : run checkEmpty r n p h k bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved), afterCache)) :
    ∃ (tries : List EqualityTrie.Trie)
        (first : Suspended) (rest descendants : List Suspended)
        (recorded : List Nat) (winner : Nat) (joined : Core)
        (foldCaller : Caller width) (foldQueries : Queries) (folded foldOuter : Core)
        (found : UnionFind.Result) (oldNode : Option Nat) (oldScs : List Suspended)
        (handle : Nat) (written : List Suspended),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      edge.children[position]? = some incoming ∧
      bucket = descendScs position parentBucket ++
        descendScs position (suspendedVars captured.core.counter tries) ∧
      bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
        (first :: rest, descendants) ∧
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest before.waiting before.core) =
        [.ok ((recorded, winner, moved), joined)] ∧
      SourcePruningEnumerationSharedCachedTerminal.rawFold
        checkEmpty n p h recorded caller joined winner queries =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, foldOuter) ∧
      folded = foldOuter ∧
      SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
        foldCaller folded winner incoming descendants foldQueries =
          (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) ∧
      fragment = .hole winner ∧
      UnionFind.findRoot r folded.representatives winner = some found ∧
      folded.values[found.representative]? = some (.unenumerated oldNode oldScs) ∧
      read = {folded with representatives := found.forest} ∧
      written =
        (descendScs position parentBucket).filter (fun sc => !EqualityTrie.isTerminal sc.trie) ++
        (descendScs position (suspendedVars captured.core.counter tries)).filter
          (fun sc => !EqualityTrie.isTerminal sc.trie) ++ oldScs ∧
      after = {read with
        values := read.values.set found.representative (.unenumerated (some handle) written)
        recursionAncestry := fun other => if other = found.representative then
          (read.expansionAncestry ++ read.recursionAncestry found.representative).eraseDups
          else read.recursionAncestry other} ∧
      after.values[found.representative]? = some (.unenumerated (some handle) written) ∧
      (∀ key, key ∈ after.recursionAncestry found.representative ↔
        key ∈ folded.expansionAncestry ∨ key ∈ folded.recursionAncestry found.representative) ∧
      ∀ occurrence sc, written[occurrence]? = some sc →
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
          (∃ (parentPosition : Nat) (original : Suspended),
            parentBucket[parentPosition]? = some original ∧
            sc.var = original.var ∧ position :: path ∈ EqualityTrie.fromPathTrie original.trie) ∨
          (∃ (ownPosition : Nat) (trie : EqualityTrie.Trie),
            tries[ownPosition]? = some trie ∧
            sc.var = captured.core.counter + ownPosition ∧
            position :: path ∈ EqualityTrie.fromPathTrie trie) ∨
          (∃ oldPosition : Nat, oldScs[oldPosition]? = some sc) := by
  have allowed : arityAllows edge.children.length parentBucket = true := by
    by_cases accepted : arityAllows edge.children.length parentBucket = true
    · exact accepted
    · simp [SourcePruningEnumerationCachedOwn.prepare, accepted] at prepared
  cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
  | none =>
      simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at prepared
  | some pair =>
      obtain ⟨tries, projectedResidual⟩ := pair
      have inputShape := SourcePruningEnumerationCachedOwn.prepare_inputs
        heap parentBucket edge captured own tries projectedResidual
        (symbol, staged, residual) projected prepared
      have residualSame : residual = projectedResidual :=
        congrArg (fun result => result.2.2) inputShape
      subst projectedResidual
      have stagedSame : staged =
          (SourcePruningEnumerationEdgeInputs.children edge parentBucket captured.core.counter tries).map
            (fun input => (input.1, input.2,
              SourcePruningEnumerationShallowChild.prepareChild
                (EnumGuard := Constraint) input.2 input.1)) :=
        congrArg (fun result => result.2.1) inputShape
      have indexedSelection := selected
      rw [stagedSame, SourcePruningEnumerationEdgeInputs.children,
        List.map_map, List.getElem?_map] at indexedSelection
      obtain ⟨indexed, indexedStored, selectedSame⟩ := Option.map_eq_some_iff.mp indexedSelection
      rw [List.getElem?_zipIdx] at indexedStored
      obtain ⟨child, childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
      have childSame : child = incoming := congrArg Prod.fst selectedSame
      have actualChild : edge.children[position]? = some incoming := by
        rw [← childSame]
        exact childStored
      have bucketSame : bucket = descendScs position parentBucket ++
          descendScs position (suspendedVars captured.core.counter tries) := by
        simpa only [Nat.zero_add] using
          (congrArg (fun input : Child => input.2.1) selectedSame).symm
      obtain ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries,
        folded, foldOuter, partitioned, prefixObserved, foldObserved, foldEndpoint,
        incomingObserved, _recordedShape, _valuesSame, fragmentSame, _aliases⟩ :=
        terminal_singleton_raw_target_incidence checkEmpty r n p h k bucket incoming
          caller before queries terminal fragment afterCaller savedQueries read after moved
          afterCache roots paths actual
      obtain ⟨found, oldNode, oldScs, handle, lookup, oldStored, readSame,
        writtenState, writtenSlot, ancestry⟩ :=
        SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history
          checkEmpty r n p h foldCaller folded winner incoming descendants foldQueries
          after afterCaller savedQueries read incomingObserved
      have descendantsSame : descendants =
          bucket.filter (fun sc => !EqualityTrie.isTerminal sc.trie) := by
        have same := congrArg Prod.snd partitioned
        simpa only [List.partition_eq_filter_filter] using same.symm
      let written : List Suspended := descendants ++ oldScs
      refine ⟨tries, first, rest, descendants, recorded, winner, joined,
        foldCaller, foldQueries, folded, foldOuter, found, oldNode, oldScs, handle, written,
        projected, actualChild, bucketSame, partitioned, prefixObserved, foldObserved,
        foldEndpoint, incomingObserved, fragmentSame, lookup, oldStored, readSame,
        ?_, writtenState, writtenSlot, ancestry, ?_⟩
      · simp only [written, descendantsSame, bucketSame, List.filter_append, List.append_assoc]
      · intro occurrence sc stored path represented
        have member : sc ∈ descendants ++ oldScs := List.mem_of_getElem? stored
        rcases List.mem_append.mp member with fresh | old
        · have filtered : sc ∈ bucket.filter (fun sc => !EqualityTrie.isTerminal sc.trie) := by
            rw [← descendantsSame]
            exact fresh
          have retained : sc ∈ bucket := (List.mem_filter.mp filtered).1
          rw [bucketSame] at retained
          rcases List.mem_append.mp retained with inherited | own
          · obtain ⟨original, originalMember, varSame, originalPath⟩ :=
              descended_occurrence_origin position parentBucket sc inherited path represented
            obtain ⟨parentPosition, parentStored⟩ := List.mem_iff_getElem?.mp originalMember
            exact Or.inl ⟨parentPosition, original, parentStored, varSame, originalPath⟩
          · obtain ⟨original, originalMember, varSame, originalPath⟩ :=
              descended_occurrence_origin position (suspendedVars captured.core.counter tries)
                sc own path represented
            obtain ⟨ownPosition, trie, ownStored, ownVariable, ownTrie⟩ :=
              suspended_occurrence_index captured.core.counter tries original originalMember
            have triePath : position :: path ∈ EqualityTrie.fromPathTrie trie := by
              rw [← ownTrie]
              exact originalPath
            exact Or.inr (Or.inl
              ⟨ownPosition, trie, ownStored, varSame.trans ownVariable, triePath⟩)
        · exact Or.inr (Or.inr (List.mem_iff_getElem?.mp old))

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch

#check @MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins
#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins
