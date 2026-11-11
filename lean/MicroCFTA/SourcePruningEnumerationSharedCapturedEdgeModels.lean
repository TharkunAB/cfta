import MicroCFTA.SourcePruningEnumerationSharedCapturedPreparedResources
import MicroCFTA.SourcePruningEnumerationSharedSelectedEdgeModels
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.EnumerationCompleteness

/-!
# A compatible model after actual shared captured-slot finalization

The current ready slot supplies its own inherited constraints.
The selected prepared row accepts the same assigned term.
Finalization writes the original captured slot at the reached native heap.
The complete resource packet supplies the only returned global memo bundle.
Pending-reference history keeps its current incoming-avoidance condition.
Callbacks and backward restoration of opaque constraints remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
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
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The same current root model completes the actual captured write and its resource packet. -/
theorem complete_models_resources_prepared
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
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv))
    (old : AssignmentOrigins whole before.core.counter assignment) :
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
      Fits (advance seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap) ∧
      ∃ (fragment : Fragment) (extended : Nat → Term Symbol),
        result = .complete fragment afterCaller savedQueries after ∧
        (∀ held < before.core.counter, extended held = assignment held) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended before.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core ∧
        Fragments.fill extended fragment = assignment uv ∧
        Fragments.fill extended fragment = extended uv ∧
        AssignmentOrigins whole after.core.counter extended ∧
        ∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc := by
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have model := EnumerationCompleteness.stored_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment before.core satisfied uv (.unenumerated (some handle) scs) stored
  simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at model
  have inherited : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := model.2
  obtain ⟨terms, shape, children, _guarded⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv)).mp accepted
  have allowed : arityAllows edge.children.length scs = true := by
    rw [children.length_eq]
    apply suspended_arity_necessary assignment edge.entry.key.symbol terms scs
    intro sc member
    simpa only [shape] using inherited sc member
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, resource⟩ :=
    complete_with_history_resources_prepared seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored
      parentAvailable parentClosed realized selected paths counts flags pending allowed
      tries residual projected fits reserved known
  have resourceRun := resource.1
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, resource, ?_⟩
  obtain ⟨rm, nm, pm, hm, km, modelCaller, middle, modelQueries, _modelFinal, _modelInventory,
    middleRoots, fragment, extended, selectedRun, _post, _querySame, _growth, middlePaths,
    storage, middleRealized, middleCounts, middleFlags, _origin, _retained, protects,
    _pendingHistory, _incomingHistory, _middleSafe, fragmentBound, _fragmentPending,
    _fragmentSeparate, _returnedFits, _returnedKnown, agree, beforeModel, middleModel,
    filled, origins, extendedHeld⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.complete_models_resources
      seed formulas solver inventory caller before checkEmpty parentEntry edges depth free
      edge scs roots memos initial parentAvailable parentClosed selected ready.safe realized
      paths counts flags bounded pending tries residual projected fits reserved known ambient
      assignment (assignment uv) whole satisfied accepted inherited old (old uv ready.inside)
  have frame := protects uv ready.inside ready.root (ready.avoids handle scs stored)
  have middleStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
    frame.value.trans stored
  obtain ⟨finishFuel, finished, finishRun, _raw, written, _finishedStored, _finishedFlag,
    _finishedWaiting, _finishedPaths, _finishedCounts, _finishedFlags, _finishedStorage,
    _finishedRealized, _finishedSafe, meaning⟩ :=
    SourcePruningEnumerationFinalize.complete_semantics modelCaller.checked.native.machine.heap
      middle uv fragment (.unenumerated (some handle) scs) middleStored middleRoots middlePaths
      middleCounts middleFlags storage fragmentBound middleRealized
  have finalModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient modelCaller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended finished.core := by
    apply (meaning _ _ extended).mpr
    refine ⟨EnumerationFrame.neutralize_satisfies _ _ extended uv middle.core middleModel, ?_⟩
    rw [filled, agree uv ready.inside]
  have finishedOrigins : AssignmentOrigins whole finished.core.counter extended := by
    rw [written]
    exact origins
  have capturedRun : ∀ er en P H ek, pm ≤ P → hm ≤ H →
      run checkEmpty (rm + er) (nm + en) P H (km + finishFuel + ek)
        uv scs edge caller before memos.query =
        some (.complete fragment modelCaller modelQueries finished) := by
    intro er en P H ek largeP largeH
    have selectedAt := selectedRun er en P H (finishFuel + ek) largeP largeH
    rw [← Nat.add_assoc] at selectedAt
    simp only [run, selectedAt]
    have finishAt := finishRun (km + ek)
    rw [show finishFuel + (km + ek) = km + finishFuel + ek by omega] at finishAt
    rw [finishAt]
  let commonR := max r rm
  let commonN := max n nm
  let commonP := max p pm
  let commonH := max h hm
  let commonK := max k (km + finishFuel)
  have resourceAt := resourceRun (commonR - r) (commonN - n) commonP commonH (commonK - k)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have modelAt := capturedRun (commonR - rm) (commonN - nm) commonP commonH
    (commonK - (km + finishFuel)) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have resourceR : r + (commonR - r) = commonR := by omega
  have resourceN : n + (commonN - n) = commonN := by omega
  have resourceK : k + (commonK - k) = commonK := by omega
  have modelR : rm + (commonR - rm) = commonR := by omega
  have modelN : nm + (commonN - nm) = commonN := by omega
  have modelK : km + finishFuel + (commonK - (km + finishFuel)) = commonK := by omega
  rw [resourceR, resourceN, resourceK] at resourceAt
  rw [modelR, modelN, modelK] at modelAt
  have resultSame : result = .complete fragment modelCaller modelQueries finished :=
    Option.some.inj (resourceAt.symm.trans modelAt)
  rcases resource with ⟨_running, _resourcePost, _resourceQuery, _resourceGrowth, _resourcePaths,
    _resourceStorage, _resourceRealized, _resourceCounts, _resourceFlags, _resourceOrigin,
    _resourcePending, _resourceProtects, _resourceHistory, resultShape, _resourceFits, _resourceKnown⟩
  rcases resultShape with ⟨resourceFragment, completed, _completePacket⟩ |
    ⟨prefixFragments, outer, waiting, stopped⟩
  · have same : resourceFragment = fragment ∧ afterCaller = modelCaller ∧
        savedQueries = modelQueries ∧ after = finished := by
      simpa only [SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete.injEq]
        using completed.symm.trans resultSame
    obtain ⟨_fragmentSame, callerSame, querySame, cacheSame⟩ := same
    refine ⟨fragment, extended, ?_, agree, beforeModel, ?_, filled, ?_, ?_, extendedHeld⟩
    · simpa only [callerSame, querySame, cacheSame] using resultSame
    · simpa only [callerSame, cacheSame] using finalModel
    · rw [filled, agree uv ready.inside]
    · simpa only [cacheSame] using finishedOrigins
  · have impossible := stopped.symm.trans resultSame
    cases impossible

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
