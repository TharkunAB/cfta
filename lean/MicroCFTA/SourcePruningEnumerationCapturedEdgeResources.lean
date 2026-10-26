import MicroCFTA.SourcePruningEnumerationCapturedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources

/-!
# Original resources through the captured-slot write

The selected edge supplies the actual returned native caller.
Finalization updates the enumeration cache and retains that caller.
The complete earlier history and resource bounds remain at the same endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Initial resources retain the full captured-slot history and its actual native caller. -/
theorem complete_with_history_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨r, n, p, h, k, afterCaller, middle, savedQueries, final, next, afterRoots, edgeResult,
    edgeRun, post, querySame, growth, middlePaths, storage, middleRealized, middleCounts,
    middleFlags, origin, retained, protects, pendingHistory, incomingHistory, shape, returnedFits, returnedKnown⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected fits reserved known
  rcases shape with ⟨fragment, completed, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · subst edgeResult
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨fuel, after, finishRun, _raw, core, finalStored, _finalFlag, _finalWaiting,
      afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
      SourcePruningEnumerationFinalize.complete afterCaller.checked.native.machine.heap middle uv fragment
        (.unenumerated (some handle) scs) currentStored afterRoots middlePaths middleCounts middleFlags
        storage fragmentBound middleRealized
    have afterSafe := safeFinish middleSafe frame.root
    have separate := fragmentSeparate uv ready.inside ready.root avoids
    have afterFragmentPending : PendingFragment after.core fragment := by
      rw [core]
      exact pendingFragment_write middle.core uv fragment fragmentPending separate
    have advance : ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
      intro level frontier stratified
      have enumProtects : ∀ held old, before.core.values[held]? = some (.enumerated old) →
          EnumerationDriver.Protected held before.core middle.core := by
        intro held old stored
        obtain ⟨inside, root⟩ := enumerated_root before.core ready.safe held old stored
        exact protects held inside root (pending held old stored)
      obtain ⟨middleLevel, middleOrder⟩ := EnumerationOrder.stratified_preserved before.core middle.core
        middleSafe level frontier stratified origin enumProtects
      obtain ⟨nextLevel, nextOrder⟩ := EnumerationOrder.write_stratified middle.core middleSafe middleLevel
        frontier uv middleOrder (some handle) scs currentStored fragment fragmentPending separate
      refine ⟨nextLevel, ?_⟩
      rw [core]
      exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) nextOrder
    have afterPending : InputsPending after.core scs := by
      intro held old expanded
      by_cases same : held = uv
      · subst held
        rw [core]
        exact frame.avoids scs avoids
      · rw [core]
        apply retained held old
        rw [core] at expanded
        simpa only [List.getElem?_set_ne (Ne.symm same)] using expanded
    refine ⟨r, n, p, h, k + fuel, afterCaller, after, savedQueries, final, next, afterRoots,
      .complete fragment afterCaller savedQueries after, ?_, post, querySame, ?_, afterPaths,
      afterStorage, afterRealized, afterCounts, afterFlags, ?_, afterPending, ?_, ?_,
      .inl ⟨fragment, rfl, afterSafe, ?_, finalStored, ?_, ?_, afterFragmentPending, advance⟩, returnedFits, returnedKnown⟩
    · intro er en P H ek largeP largeH
      have selectedRun := edgeRun er en P H (fuel + ek) largeP largeH
      rw [← Nat.add_assoc] at selectedRun
      simp only [run, selectedRun]
      have finalRun := finishRun (k + ek)
      rw [show fuel + (k + ek) = k + fuel + ek by omega] at finalRun
      rw [finalRun]
      rfl
    · rw [core]
      exact growth
    · intro held old different expanded
      apply origin held old
      rw [core] at expanded
      simpa only [List.getElem?_set_ne (Ne.symm different)] using expanded
    · intro held different inside root separate
      have oldFrame := protects held inside root separate
      apply oldFrame.trans
      refine ⟨?_, ?_, ?_⟩
      · rw [core]
        exact List.getElem?_set_ne (Ne.symm different)
      · rw [core]
        exact oldFrame.root
      · rw [core]
        exact fun _ => Iff.rfl
    · intro history incoming
      have written := EnumerationReferences.setValue_pending uv fragment middle.core
        {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
        (pendingHistory history) (incomingHistory uv ready.inside ready.root avoids incoming)
        ((EnumerationDriver.modify_success _ _ _).mpr rfl)
      rw [core]
      exact written
    · rw [core]
      exact fragmentBound
    · rw [core]
    · rw [core]
      exact frame.root
  · subst edgeResult
    refine ⟨r, n, p, h, k, afterCaller, middle, savedQueries, final, next, afterRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some middle),
      ?_, post, querySame, growth, middlePaths, storage, middleRealized, middleCounts, middleFlags,
      fun held old _ expanded => origin held old expanded, retained,
      fun held _ inside root separate => protects held inside root separate,
      (fun history _ => pendingHistory history),
      .inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown⟩
    intro er en P H ek largeP largeH
    rw [run, edgeRun er en P H ek largeP largeH]

/-- Initial resources retain the complete earlier captured-slot interface. -/
theorem complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, queries, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, retained, protects, pendingHistory, shape, returnedFits, returnedKnown⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry edges depth free
      edge roots memos initial ready stored decoded realized selected paths counts flags pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, queries, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, retained, protects, pendingHistory, ?_, returnedFits, returnedKnown⟩
  rcases shape with ⟨fragment, completed, afterSafe, fragmentBound, finalStored, ancestry, root, _history⟩ | stopped
  · exact .inl ⟨fragment, completed, afterSafe, fragmentBound, finalStored, ancestry, root⟩
  · exact .inr stopped

end MicroCFTA.SourcePruningEnumerationCapturedEdge
