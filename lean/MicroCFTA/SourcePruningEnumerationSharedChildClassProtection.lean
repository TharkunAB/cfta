import MicroCFTA.SourcePruningEnumerationSharedChildIsolation
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets
import MicroCFTA.SourcePruningEnumerationSharedIncomingBucketHistory
import MicroCFTA.SourcePruningEnumerationPreparedSharedChildIsolation

/-!
# Complete class protection at actual shared child success

The actual terminal prefix excludes the held class from every join.
The shared fold retains its representative forest.
The incoming call performs actual path compression and one value write.
Their composition retains the complete held class at the returned cache.
The existing isolation theorem supplies the same root, native handle and empty bucket.
All supplied budgets and endpoints remain those of the observed child call.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildIsolation
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDischargeHistory EnumerationReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)

set_option autoImplicit false
variable {bits : Nat}

/-- The same actual shared child singleton protects every member of the original isolated class. -/
theorem observed_protected_isolated_pending
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before middle : Cached) (queries saved : Queries)
    (fragment : Fragment) (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (held heldHandle : Nat)
    (safe : Safe before.core)
    (isolated : EnumerationDischargeHistory.IsolatedPending held heldHandle before.core)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (inputs : Avoids before.core.representatives held scs)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs value caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some middle)) :
    EnumerationDriver.Protected held before.core middle.core ∧
      EnumerationDischargeHistory.IsolatedPending held heldHandle middle.core := by
  have finalIsolated := observed_isolated_pending checkEmpty r n p h k scs value
    caller reached before middle queries saved fragment returned outer waiting held heldHandle
    safe isolated bounded inputs observed
  have coreSame := SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.singleton_core
    checkEmpty r n p h k scs value caller reached before middle
    queries saved fragment returned outer waiting observed
  have classes : ∀ other, UnionFind.SameClass middle.core.representatives held other ↔
      UnionFind.SameClass before.core.representatives held other := by
    rw [coreSame]
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · obtain ⟨roots, paths⟩ := roots_exist before.core.representatives safe.1.total
      obtain ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries,
        folded, _foldOuter, partitioned, processed, _foldedCall, _foldEndpoint, incomingCall,
        _recordedSame, _joinedValues, _hole, foldedForest, returnedForest, _rawTargets⟩ :=
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_final_raw_target_incidence
          checkEmpty r n p h k scs value caller before queries terminal fragment reached saved
          outer returned waiting (some middle) roots paths observed
      have active : Avoids before.core.representatives held (first :: rest) := by
        intro sc member
        have here : sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 := by
          simpa only [partitioned] using member
        have filtered : sc ∈ scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
          simpa only [List.partition_eq_filter_filter] using here
        exact inputs sc (List.mem_filter.mp filtered).1
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, waiting) joined := by
        rw [Success, processed]
        exact List.mem_singleton_self _
      obtain ⟨joinedTotal, _joinedIsolated, _recordedOther, _winnerOther, joinedClasses⟩ :=
        SourcePruningEnumerationTerminalPrefix.run_isolated r held heldHandle first rest before.waiting
          before.core joined recorded winner waiting safe.1.total isolated active prefixSuccess
      have foldedTotal : UnionFind.Total folded.representatives := by
        rw [foldedForest]
        exact joinedTotal
      obtain ⟨found, _oldNode, _oldScs, _handle, lookup, _stored, readSame,
        _written, _writtenSlot, _ancestry⟩ :=
        SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history
          checkEmpty r n p h foldCaller folded winner value descendants foldQueries
          returned reached saved outer incomingCall
      intro other
      rw [returnedForest, readSame]
      exact (UnionFind.findRoot_classes foldedTotal lookup held other).trans (by
        rw [foldedForest]
        exact joinedClasses other)
    · have original :=
        (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.erase
          checkEmpty r n p h k scs value caller before queries).symm.trans
          (congrArg Prod.fst observed)
      by_cases empty : value = .empty
      · simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe,
          empty, ↓reduceIte] at original
        cases original
      · have noTerminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
          Bool.eq_false_iff.mpr terminal
        have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
          simp only [List.partition_eq_filter_filter]
          exact List.filter_eq_nil_iff.mpr (List.any_eq_false.mp noTerminal)
        cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
        | mk here descendants =>
          have hereSame : here = [] := by
            first
            | exact noHere
            | exact (congrArg Prod.fst partitioned).symm.trans noHere
          subst here
          simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe,
            empty, ↓reduceIte, partitioned] at original
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) scs value with
          | none => simp only [prepared] at original; cases original
          | some action =>
            rw [prepared] at original
            have rawSame := congrArg Prod.fst original
            dsimp only at rawSame
            have success : Success action before.core fragment returned := by
              rw [Success, Option.some.inj (Except.ok.inj rawSame)]
              exact List.mem_singleton_self _
            have inside : held < before.core.counter := by
              rw [safe.1.aligned]
              exact (List.getElem?_eq_some_iff.mp isolated.stored).1
            have protectedRoot := (SourcePruningEnumerationChildEffects.child scs value action
              before.core returned fragment safe bounded prepared success).2.2 held inside isolated.root
            exact protectedRoot.classes
  exact ⟨⟨finalIsolated.stored.trans isolated.stored.symm, finalIsolated.root, classes⟩,
    finalIsolated⟩

/-- Actual preparation and shared child success protect the same complete original class. -/
theorem prepared_stored_child_protected
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (caller reached : Caller (bits + 2)) (captured own after : Cached)
    (parentOwner : Nat) (parentNode : Option Nat) (parentBucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (symbol : Symbol) (staged : List Child)
    (residual : Option Constraint) (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (checkEmpty : Bool) (r n p h k : Nat) (queries saved : Queries)
    (fragment : Fragment) (returned outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (held heldHandle : Nat) (safe : Safe captured.core)
    (isolated : IsolatedPending held heldHandle captured.core)
    (parentStored : captured.core.values[parentOwner]? = some (.unenumerated parentNode parentBucket))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap
      parentBucket edge captured = some [((symbol, staged, residual), own)])
    (selected : staged[position]? = some (incoming, bucket, action))
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming caller own queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after)) :
    EnumerationDriver.Protected held captured.core after.core ∧
      IsolatedPending held heldHandle after.core := by
  obtain ⟨preparedProtection, ownIsolated, bucketAvoids, ownSafe, bucketBounded⟩ :=
    SourcePruningEnumerationPreparedSharedChildIsolation.prepared_stored_child_inputs
      caller captured own parentOwner parentNode parentBucket edge symbol staged residual
      position incoming bucket action held heldHandle safe isolated parentStored prepared selected
  obtain ⟨childProtection, childIsolated⟩ := observed_protected_isolated_pending
    checkEmpty r n p h k bucket incoming caller reached own after queries saved fragment returned
    outer waiting held heldHandle ownSafe ownIsolated bucketBounded bucketAvoids actual
  exact ⟨preparedProtection.trans childProtection, childIsolated⟩

end MicroCFTA.SourcePruningEnumerationSharedChildIsolation
