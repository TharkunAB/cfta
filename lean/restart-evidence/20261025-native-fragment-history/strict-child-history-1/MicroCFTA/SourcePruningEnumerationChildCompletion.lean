import MicroCFTA.SourcePruningEnumerationChildTraversal
import MicroCFTA.EnumerationFragmentHistory

namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
variable {width : Nat}

/-- Only a nonempty terminal head requires numeric native-request admission. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  incoming ≠ .empty → ∀ first rest descendants,
    bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) = (first :: rest, descendants) →
    SourcePruningEnumerationCachedTerminalAdapter.Ranges checkEmpty first rest caller before incoming queries

private theorem partition_subsets (bucket : List Suspended) (first : Suspended)
    (rest descendants : List Suspended)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants)) : (first :: rest) ⊆ bucket ∧ descendants ⊆ bucket := by
  have terminal : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  have other : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
    simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
  exact ⟨fun _ member => (List.mem_filter.mp (terminal ▸ member)).1,
    fun _ member => (List.mem_filter.mp (other ▸ member)).1⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem nonterminal_parameters
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (nonempty : incoming ≠ .empty)
    (partitioned : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = []) :
    SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller before queries =
      SourcePruningEnumerationChildDispatch.run checkEmpty 0 0 0 0 k bucket incoming caller before queries := by
  cases splitBucket : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
    have empty : here = [] := by simpa only [splitBucket] using partitioned
    subst here
    simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
      ite_eq_right nonempty, splitBucket]

/-- Genuine admitted child inputs retain pending targets and separation for returned holes. -/
theorem complete_with_fragments
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (ranges : Ranges checkEmpty bucket incoming beforeCaller before memos.query) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller width) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment) := by
  by_cases empty : incoming = .empty
  · subst incoming
    refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
      before.core, before.waiting, ?_, Post.refl initial, rfl, Nat.le_refl _, paths, safe.1,
      realized, counts, flags, .refl _, ?_, (fun _ valid _ => valid), (fun valid => valid), .inl rfl⟩
    · intro er en P H ek _ _
      exact SourcePruningEnumerationChildDispatch.empty checkEmpty _ _ _ _ _ _ _ _ _
    · intro held _ root _
      exact EnumerationDriver.Protected.refl held before.core root
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        have noHere : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
          rw [partitioned]
        have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
          have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
            simpa only [List.partition_eq_filter_filter] using noHere
          exact List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
        obtain ⟨action, k, after, prepared, rawRun, observed, grows, _aligned,
          forestSame, afterPaths, storage, afterRealized, afterCounts, afterFlags, bound⟩ :=
          SourcePruningEnumerationChildDispatch.nonterminal_complete checkEmpty 0 0 0 0 bucket incoming
            beforeCaller before memos.query roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent
            available closed empty safe.1 realized paths counts flags bounded noTerminal
        have success : Success action before.core (.hole before.core.counter) after.core := by
          rw [Success, rawRun]
          simp
        obtain ⟨afterSafe, origin, protects⟩ := SourcePruningEnumerationChildEffects.child
          bucket incoming action before.core after.core _ safe bounded prepared success
        have freshPath : UnionFind.Reaches after.core.representatives
            before.core.counter before.core.counter 1 := by
          rw [forestSame]
          exact .root (by simp [UnionFind.read, outside_forest before.core.representatives
            before.core.counter before.core.counter safe.1.forest (Nat.le_refl _)])
        have index : before.core.counter < after.core.values.length := by
          rw [← afterSafe.1.aligned]
          omega
        let value := after.core.values[before.core.counter]
        have stored : after.core.values[before.core.counter]? = some value :=
          List.getElem?_eq_getElem index
        have live : value ≠ .eliminated :=
          (afterSafe.2 before.core.counter value stored).mpr ⟨1, freshPath⟩
        have fragmentPending : PendingFragment after.core (.hole before.core.counter) := by
          cases valueEq : value with
          | eliminated => exact (live valueEq).elim
          | unenumerated node scs =>
              exact pendingFragment_hole after.core before.core.counter before.core.counter 1
                node scs freshPath (by simpa [valueEq] using stored)
          | enumerated fragment =>
              have oldStored := origin before.core.counter fragment (by simpa [valueEq] using stored)
              have inside := (enumerated_root before.core safe before.core.counter fragment oldStored).1
              omega
        have separate : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
            Avoids before.core.representatives held bucket →
            FragmentAvoid after.core.representatives held (.hole before.core.counter) := by
          intro held inside _root _avoids uv hole related
          cases hole
          rw [forestSame] at related
          have same := outside_class before.core.representatives before.core.counter
            before.core.counter held safe.1.forest (Nat.le_refl _)
            (UnionFind.sameClass_symm related)
          omega
        have references : ∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
            EnumerationReferences.InputsAllowed allowed bucket →
            EnumerationReferences.ReferencesAllowed allowed after.core := by
          intro allowed valid inputs
          exact SourcePruningEnumerationNativeReferences.prepared_allowed allowed bucket incoming action
            before.core after.core _ valid inputs prepared success
        have global : EnumerationReferences.PendingReferences before.core →
            EnumerationReferences.PendingReferences after.core := by
          intro history
          apply SourcePruningEnumerationNativeReferences.pending_preserved before.core after.core bucket
            history pending origin _ references
          intro held fragment stored
          obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment stored
          exact protects held inside root
        refine ⟨0, 0, 0, 0, k, [.ok (.hole before.core.counter, after.core)], beforeCaller, after,
          memos.query, memos, inventory, roots, before.core, before.waiting, ?_, Post.refl initial,
          rfl, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags, origin, ?_, references, global,
          .inr ⟨.hole before.core.counter, rfl, afterSafe, bound, fragmentPending, separate⟩⟩
        · intro er en P H ek _ _
          rw [nonterminal_parameters checkEmpty _ _ _ _ _ bucket incoming beforeCaller before memos.query empty noHere]
          exact observed ek
        · omega
        · intro held inside root _
          exact protects held inside root
      | cons first rest =>
        have subsets := partition_subsets bucket first rest descendants partitioned
        have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
          fun sc member => bounded sc (subsets.1 member)
        have activePending : InputsPending before.core (first :: rest) := by
          intro held fragment stored sc member
          exact pending held fragment stored sc (subsets.1 member)
        obtain ⟨r, n, p, h, k, recorded, winner, joined, foldRows, foldCaller, foldQueries,
          foldFinal, foldInventory, folded, raw, afterCaller, outer, savedQueries, final, next, after,
          _prefixRun, recordedSame, winnerMember, _movedSame, _joinedSame, _joinedFlagsSame,
          _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun, foldShape, _foldPost,
          _foldQuerySame, _foldCounter, _foldForest, _foldPaths, _foldStorage, _foldRealized, _foldedRoot,
          _foldPending, _foldCounts, _foldWaiting, _foldFlags, _foldEliminated, _foldCompleted,
          _foldedFrame, _foldedSafe, _foldedOrigin, _terminalRun, post, querySame, cacheRun,
          counter, afterPaths, storage, afterRealized, afterCounts, afterFlags, _outside,
          afterSafe, protects, origin, references, _rejectedCache, rejected, completed⟩ :=
          SourcePruningEnumerationCachedTerminalAdapter.complete formulas solver inventory beforeCaller before
            checkEmpty first rest incoming descendants roots memos initial safe paths counts flags
            activeBounded activePending realized empty available closed
            (fun sc member => bounded sc (subsets.2 member))
            (ranges empty first rest descendants partitioned)
        have fullReferences : ∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
            EnumerationReferences.InputsAllowed allowed bucket →
            EnumerationReferences.ReferencesAllowed allowed after.core := by
          intro allowed valid inputs
          exact references allowed valid (fun sc member => inputs sc (subsets.2 member))
        have global : EnumerationReferences.PendingReferences before.core →
            EnumerationReferences.PendingReferences after.core := by
          intro history
          apply SourcePruningEnumerationNativeReferences.pending_preserved before.core after.core bucket
            history pending origin _ fullReferences
          intro held fragment stored
          have root := (enumerated_root before.core safe held fragment stored).2
          exact protects held root (fun sc member => pending held fragment stored sc (subsets.1 member))
        refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next,
          EnumerationCanonicalUnion.mergedRoots roots recorded winner, outer, joined.waiting,
          ?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags, origin,
          ?_, fullReferences, global, ?_⟩
        · intro er en P H ek largeP largeH
          rw [SourcePruningEnumerationChildDispatch.terminal checkEmpty _ _ _ _ _ bucket incoming
            beforeCaller before memos.query first rest descendants partitioned]
          exact cacheRun er en P H ek largeP largeH
        · omega
        · intro held _ root avoids
          exact protects held root (fun sc member => avoids sc (subsets.1 member))
        · rcases foldShape with rejectedFold | completedFold
          · exact .inl (rejected rejectedFold).1
          · obtain ⟨incomingK, oldNode, oldScs, read, incomingAfter, replacement, handle,
              afterSame, _outerSame, _readRun, _readFrame, _incomingRun, _writeRun,
              _writeShape, winnerStored, _storage, _realized, _post, _unfolding, _writeCache,
              _counter, _representatives, _paths, _counts, _waiting, _flags, _expandable,
              rawSame, bound, _available, _closed, _encoded, _lookup, _unconstrained, _constrained⟩ :=
              completed completedFold
            subst incomingAfter
            by_cases rejectedIncoming : replacement = .empty
            · exact .inl (by simpa only [rejectedIncoming, ↓reduceIte] using rawSame)
            · have singleton : raw = [.ok (.hole winner, after.core)] := by
                simpa only [rejectedIncoming, ↓reduceIte] using rawSame
              have finalSafe := afterSafe (by simp [singleton])
              obtain ⟨winnerSize, winnerPath⟩ :=
                (finalSafe.2 winner _ winnerStored).mp (by simp)
              refine .inr ⟨.hole winner, singleton, finalSafe, bound,
                pendingFragment_hole after.core winner winner winnerSize (some handle)
                  (descendants ++ oldScs) winnerPath winnerStored, ?_⟩
              intro held _inside root avoids uv hole related
              cases hole
              have activeAvoid : Avoids before.core.representatives held (first :: rest) :=
                fun sc member => avoids sc (subsets.1 member)
              have fixed : roots held = held := (root_iff _ roots paths held).mp root
              have outside : held ∉ recorded := by
                intro member
                rw [recordedSame] at member
                obtain ⟨sc, scMember, named⟩ := List.mem_map.mp member
                exact activeAvoid sc scMember
                  ((class_iff _ roots paths held sc.var).mpr (fixed.trans named.symm))
              obtain ⟨_heldSize, heldPath⟩ := (protects held root activeAvoid).root
              have same := (UnionFind.sameClass_iff_roots heldPath winnerPath).mp related
              exact outside (same.symm ▸ winnerMember)

/-- Genuine admitted child inputs derive a stable singleton or a valid empty rejection. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (ranges : Ranges checkEmpty bucket incoming beforeCaller before memos.query) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller width) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment) := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, references, history, shape⟩ :=
    complete_with_fragments formulas solver inventory beforeCaller before checkEmpty bucket incoming
      roots memos initial safe paths counts flags realized bounded pending available closed ranges
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, references, history, ?_⟩
  rcases shape with rejected | ⟨fragment, singleton, afterSafe, bound, _pending, _separate⟩
  · exact .inl rejected
  · exact .inr ⟨fragment, singleton, afterSafe, bound⟩

end MicroCFTA.SourcePruningEnumerationChildCompletion
