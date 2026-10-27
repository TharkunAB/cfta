import MicroCFTA.SourcePruningEnumerationSelectedEdgeProper
import MicroCFTA.SourcePruningEnumerationTraversalEndpointProper
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources

/-!
# Proper storage at actual selected-edge endpoints

The own prefix supplies the actual child inputs and cache.
A stopped child retains its actual optional cache.
The complete original resource packet precedes the new proper-state observer.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationSemantics EnumerationProgress Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual complete and attached stopped results preserve proper pending paths. -/
theorem observed_cache_proper
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (proper : ProperState before.core) (inherited : ValidSuspended scs)
    {r n p h k : Nat} {result : Result width}
    (observed : run checkEmpty r n p h k scs edge caller before memos.query = result) :
    match result with
    | .complete _ _ _ after | .rejected _ _ after => ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, _ownCounter, _ownForest,
    _ownSafe, _ownPaths, _ownRealized, _ownCounts, _ownFlags, _combinedPending, _genuine,
    _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  have ownProperState : ProperState own.core := by
    rw [ownCore]
    exact suspension_proper tries.length before.core proper
  have triesValid := (SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
    caller.checked.native.machine.heap parentEntry edges depth free edge
    initial.ready.semantic.ready initial.annotation_heap parentAvailable selected tries residual projected).1
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have inputsProper : ∀ incoming bucket, (incoming, bucket) ∈ inputs → ProperInputs bucket :=
    children_proper_inputs edge scs before.core.counter tries inherited triesValid
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  simp only [run, ownRun] at observed
  rw [readback] at observed
  cases childrenRun : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      inputs caller own memos.query with
  | stopped fragments observation candidate =>
      rw [childrenRun] at observed
      cases observed
      exact SourcePruningEnumerationChildTraversal.observed_cache_proper
        ownProperState inputsProper childrenRun
  | complete fragments reachedCaller saved reached =>
      rw [childrenRun] at observed
      cases observed
      exact finish_proper residual (.node edge.entry.key.symbol fragments) reached
        (SourcePruningEnumerationChildTraversal.complete_proper ownProperState inputsProper childrenRun)

variable {bits : Nat}
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- Keep every original resource field and derive proper storage at its returned cache. -/
theorem complete_with_fragments_resources_proper
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      ((∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧ InputsPending after.core scs ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationReferences.IncomingAvoid held before.core →
        EnumerationReferences.IncomingAvoid held after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
          ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
            Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap) ∧
      (ProperState before.core → ValidSuspended scs → ProperState after.core) := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial parentAvailable parentClosed selected
      safe realized paths counts flags bounded pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet, ?_⟩
  intro proper inherited
  rcases packet with ⟨running, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _retained, _protects, _pendingHistory, _incomingHistory,
    shape, _returnedFits, _returnedKnown⟩
  have actual : run checkEmpty r n p h k scs edge caller before memos.query = result := by
    simpa only [Nat.add_zero] using running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have resultProper := observed_cache_proper caller before checkEmpty parentEntry edges depth free
    edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
    bounded pending allowed tries residual projected proper inherited actual
  rcases shape with ⟨fragment, completed, _rest⟩ | ⟨fragments, outer, waiting, stopped⟩
  · simpa only [completed] using resultProper
  · simpa only [stopped] using resultProper

end MicroCFTA.SourcePruningEnumerationSelectedEdge
