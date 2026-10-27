import MicroCFTA.SourcePruningEnumerationCapturedEdgeProper
import MicroCFTA.SourcePruningEnumerationSelectedEdgeEndpointProper
import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources

/-!
# Proper storage at actual captured-edge endpoints

The stored pending bucket supplies inherited validity.
A stopped result retains the actual cache without a finalizer write.
A complete result preserves proper storage through its same finalizer.
The complete original resource packet remains before the new observer.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationProgress EnumerationSemantics EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual complete and attached stopped captured results preserve proper pending paths. -/
theorem observed_cache_proper
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
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
    (proper : ProperState before.core)
    {r n p h k : Nat} {result : Result width}
    (observed : run checkEmpty r n p h k uv scs edge caller before memos.query = some result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after => ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have inheritedInputs : ProperInputs scs :=
    proper_inputs (.unenumerated (some handle) scs) (proper _ (List.mem_of_getElem? stored))
  have inherited : ValidSuspended scs := fun sc member => (inheritedInputs sc member).1
  unfold run at observed
  cases selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k
      scs edge caller before memos.query with
  | unhandled =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      trivial
  | rejected reachedCaller saved reached =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_proper caller before checkEmpty
        parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe
        realized paths counts flags bounded pending allowed tries residual projected proper inherited selectedRun
  | stopped fragments observation candidate =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_proper caller before checkEmpty
        parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe
        realized paths counts flags bounded pending allowed tries residual projected proper inherited selectedRun
  | complete fragment reachedCaller saved reached =>
      rw [selectedRun] at observed
      simp only [Option.map_eq_some_iff] at observed
      obtain ⟨finished, finishRun, fields⟩ := observed
      cases fields
      exact SourcePruningEnumerationFinalize.run_proper reachedCaller.checked.native.machine.heap k uv
        fragment reached finished
        (SourcePruningEnumerationSelectedEdge.complete_proper caller before checkEmpty parentEntry edges depth free
          edge scs roots memos initial available closed selected ready.safe realized paths counts flags bounded
          pending allowed tries residual projected proper inherited selectedRun) finishRun

variable {bits : Nat}
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- Keep every original captured resource field and derive proper storage at its actual cache. -/
theorem complete_with_history_resources_proper
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
      ((∀ er en P H ek, p ≤ P → h ≤ H →
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
        afterCaller.checked.native.machine.heap) ∧
      (ProperState before.core → ProperState after.core) := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected paths counts
      flags pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet, ?_⟩
  intro proper
  rcases packet with ⟨running, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _retained, _protects, _pendingHistory,
    shape, _returnedFits, _returnedKnown⟩
  have actual : run checkEmpty r n p h k uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_zero] using running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have resultProper := observed_cache_proper formulas solver inventory caller before checkEmpty uv handle
    scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected paths
    counts flags pending allowed tries residual projected proper actual
  rcases shape with ⟨fragment, completed, _rest⟩ | ⟨fragments, outer, waiting, stopped⟩
  · simpa only [completed] using resultProper
  · simpa only [stopped] using resultProper

end MicroCFTA.SourcePruningEnumerationCapturedEdge
