import MicroCFTA.SourcePruningEnumerationSharedChildResources
import MicroCFTA.SourcePruningEnumerationSharedNonterminalChildModels
import MicroCFTA.SourcePruningEnumerationSharedTerminalChildModels

/-!
# One forward model at the actual shared child's resource endpoint

The resource packet retains its full returned caller, cache and global bundle.
Both model branches meet that packet at the same literal shared run.
Nonterminal children install one fresh term. Terminal children keep the assignment.
Opaque child slots can drop constraints. This theorem proves forward existence.
The shallow child operation still needs a simulation for Haskell's recursive child API.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationOrigins
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A compatible original term gives one model at the same complete child resource packet. -/
theorem complete_models_origins_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
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
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (whole chosen : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core)
    (accepted : InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
      ambient incoming chosen)
    (held : ∀ sc ∈ bucket, Suspended.Holds assignment chosen sc)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (origin : Origin whole chosen) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
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
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap) ∧
      ∃ (extended : Nat → Term Symbol) (fragment : Fragment),
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core ∧
        raw = [.ok (fragment, after.core)] ∧
        Fragments.fill extended fragment = chosen ∧
        AssignmentOrigins whole after.core.counter extended ∧
        ∀ sc ∈ bucket, Suspended.Holds extended chosen sc := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, resource⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before
      checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded
      pending available closed fits reserved known
  have resourceRun := resource.1
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, resource, ?_⟩
  have nonempty : incoming ≠ .empty := by
    intro same
    subst incoming
    simp only [InternedGuardedLanguage.meaning] at accepted
  cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
    cases here with
    | nil =>
      have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
        simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
      have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
        List.any_eq_false.mpr (List.filter_eq_nil_iff.mp filtered)
      obtain ⟨_action, km, modelAfter, extended, _prepared, _actionRun, modelRun,
        _counter, _aligned, _forestSame, _afterPaths, _storage, _realized, _counts, _flags,
        _bound, _installed, agree, beforeModel, afterModel, extendedHeld, filled, origins⟩ :=
        nonterminal_models_origins checkEmpty r n p h bucket incoming beforeCaller before
          memos.query roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent
          available closed safe.1 realized paths counts flags bounded noTerminal
          (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning assignment
          whole chosen satisfied accepted held old origin
      let common := max k km
      have resourceAt := resourceRun 0 0 p h (common - k) (Nat.le_refl _) (Nat.le_refl _)
      have modelAt := modelRun (common - km)
      have resourceIndex : k + (common - k) = common := by omega
      have modelIndex : km + (common - km) = common := by omega
      simp only [Nat.add_zero, resourceIndex] at resourceAt
      rw [modelIndex] at modelAt
      have same : raw = [.ok (.hole before.core.counter, modelAfter.core)] ∧
          afterCaller = beforeCaller ∧ savedQueries = memos.query ∧ outer = before.core ∧
          waiting = before.waiting ∧ after = modelAfter := by
        simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
          resourceAt.symm.trans modelAt
      obtain ⟨rawSame, callerSame, _querySame, _outerSame, _waitingSame, cacheSame⟩ := same
      refine ⟨extended, .hole before.core.counter, agree, beforeModel, ?_, ?_, filled, ?_, extendedHeld⟩
      · simpa only [callerSame, cacheSame] using afterModel
      · simpa only [cacheSame] using rawSame
      · simpa only [cacheSame] using origins
    | cons first rest =>
      have terminalFilter : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) =
          first :: rest := by
        simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
      have descendantFilter : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) =
          descendants := by
        simpa only [List.partition_eq_filter_filter, Function.comp_def] using
          congrArg Prod.snd partitioned
      have terminalSubset : (first :: rest) ⊆ bucket := by
        intro sc member
        exact (List.mem_filter.mp (terminalFilter ▸ member)).1
      have descendantSubset : descendants ⊆ bucket := by
        intro sc member
        exact (List.mem_filter.mp (descendantFilter ▸ member)).1
      have terminal : ∀ sc ∈ first :: rest, EqualityTrie.isTerminal sc.trie = true := by
        intro sc member
        have memberFiltered : sc ∈ bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) :=
          terminalFilter ▸ member
        exact (List.mem_filter.mp memberFiltered).2
      have terminalPending : InputsPending before.core (first :: rest) := by
        intro target fragment stored sc member
        exact pending target fragment stored sc (terminalSubset member)
      have ranges := initial_ranges seed formulas solver inventory beforeCaller before
        checkEmpty bucket incoming roots memos initial safe paths counts bounded pending
        realized available closed fits reserved known
      obtain ⟨rm, nm, pm, hm, km, _recorded, winner, joined, _foldRows, _foldCaller, _foldQueries,
        _foldFinal, _foldInventory, _folded, modelRaw, modelCaller, modelOuter, modelQueries,
        _modelFinal, _modelInventory, modelAfter, receipt, singleton, afterModel, filled, origins⟩ :=
        SourcePruningEnumerationSharedCachedTerminal.complete_forward_models formulas solver
          inventory beforeCaller before checkEmpty first rest incoming descendants roots memos
          initial safe paths counts flags (fun sc member => bounded sc (terminalSubset member))
          terminalPending realized available closed
          (fun sc member => bounded sc (descendantSubset member))
          (ranges nonempty first rest descendants partitioned) terminal ambient residualMeaning
          assignment chosen satisfied accepted
          (fun sc member => held sc (terminalSubset member))
          (fun sc member => held sc (descendantSubset member)) whole old
      rcases receipt with ⟨_prefixRun, _recordedSame, _winnerMember, _movedSame, _joinedSame,
        _joinedFlagsSame, _prefixRoots, _prefixCounts, _joinedFlags, _cachedFoldRun, _foldRun,
        _foldShape, _foldPost, _foldQuerySame, _foldCounter, _foldForest, _foldPaths,
        _foldStorage, _foldRealized, _foldedRoot, _foldPending, _foldCounts, _foldWaiting,
        _foldFlags, _foldEliminated, _foldCompleted, _foldedFrame, _foldedSafe, _foldedOrigin,
        _terminalRun, _post, _querySame, modelRun, _remaining⟩
      let rMax := max r rm
      let nMax := max n nm
      let pMax := max p pm
      let hMax := max h hm
      let kMax := max k km
      have resourceAt := resourceRun (rMax - r) (nMax - n) pMax hMax (kMax - k)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have modelAt := modelRun (rMax - rm) (nMax - nm) pMax hMax (kMax - km)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have resourceR : r + (rMax - r) = rMax := by omega
      have resourceN : n + (nMax - n) = nMax := by omega
      have resourceK : k + (kMax - k) = kMax := by omega
      have modelR : rm + (rMax - rm) = rMax := by omega
      have modelN : nm + (nMax - nm) = nMax := by omega
      have modelK : km + (kMax - km) = kMax := by omega
      rw [resourceR, resourceN, resourceK] at resourceAt
      rw [modelR, modelN, modelK] at modelAt
      have terminalAt : run checkEmpty rMax nMax pMax hMax kMax bucket incoming
          beforeCaller before memos.query =
          ((.ok (some modelRaw), modelCaller, modelQueries, modelOuter, joined.waiting),
            some modelAfter) := by
        rw [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal
          checkEmpty rMax nMax pMax hMax kMax bucket incoming beforeCaller before memos.query
          first rest descendants partitioned]
        exact modelAt
      have same : raw = modelRaw ∧ afterCaller = modelCaller ∧ savedQueries = modelQueries ∧
          outer = modelOuter ∧ waiting = joined.waiting ∧ after = modelAfter := by
        simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
          resourceAt.symm.trans terminalAt
      obtain ⟨rawSame, callerSame, _querySame, _outerSame, _waitingSame, cacheSame⟩ := same
      refine ⟨assignment, .hole winner, (fun _ _ => rfl), satisfied, ?_, ?_, filled, ?_, held⟩
      · simpa only [callerSame, cacheSame] using afterModel
      · simpa only [rawSame, cacheSame] using singleton
      · simpa only [cacheSame] using origins

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
