import MicroCFTA.SourcePruningEnumerationSharedCapturedEdgeModels
import MicroCFTA.SourcePruningEnumerationSharedSelectedPendingSize

/-!
# Strict pending work decrease at one actual shared captured edge

The current model producer supplies the only returned assignment and memos.
A plain selected receipt derives the protected pending slot before finalization.
Both receipts describe the same literal execution at common bounds.
This law concerns a completed ordinary captured step, before its callback.
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

/-- The same completed captured packet strictly lowers its assigned pending work. -/
theorem complete_models_resources_pendingSize_prepared
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
        (∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
        EnumerationStorageProgress.pendingSize after.core extended + 1 ≤
          EnumerationStorageProgress.pendingSize before.core assignment := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, resource, fragment, extended, completed, agree, beforeModel, afterModel,
    filledOriginal, filled, origins, inherited⟩ :=
    complete_models_resources_prepared seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored
      parentAvailable parentClosed realized selected paths counts flags pending tries residual
      projected fits reserved known ambient assignment whole satisfied accepted old
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, resource, fragment, extended, completed, agree, beforeModel, afterModel,
    filledOriginal, filled, origins, inherited, ?_⟩
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have model := EnumerationCompleteness.stored_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment before.core satisfied uv (.unenumerated (some handle) scs) stored
  simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at model
  have originalHeld : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := model.2
  obtain ⟨terms, termShape, children, _guarded⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv)).mp accepted
  have allowed : arityAllows edge.children.length scs = true := by
    rw [children.length_eq]
    apply suspended_arity_necessary assignment edge.entry.key.symbol terms scs
    intro sc member
    simpa only [termShape] using originalHeld sc member
  obtain ⟨sr, sn, sp, sh, sk, selectedCaller, middle, selectedQueries, _selectedFinal,
    _selectedInventory, _selectedRoots, selectedResult, selectedResource⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.complete_with_fragments_resources
      seed formulas solver inventory caller before checkEmpty parentEntry edges depth free
      edge scs roots memos initial parentAvailable parentClosed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected fits reserved known
  rcases selectedResource with ⟨selectedStable, _selectedPost, _querySame, _growth,
    _paths, _storage, _realized, _counts, _flags, _origin, _pending, protects,
    _history, _incoming, selectedShape, _returnedFits, _returnedKnown⟩
  let commonR := max r sr
  let commonN := max n sn
  let commonP := max p sp
  let commonH := max h sh
  let commonK := max k sk
  have capturedActual := resource.1 (commonR - r) (commonN - n) commonP commonH (commonK - k)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have selectedActual := selectedStable (commonR - sr) (commonN - sn) commonP commonH (commonK - sk)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have capturedR : r + (commonR - r) = commonR := by omega
  have capturedN : n + (commonN - n) = commonN := by omega
  have capturedK : k + (commonK - k) = commonK := by omega
  have selectedR : sr + (commonR - sr) = commonR := by omega
  have selectedN : sn + (commonN - sn) = commonN := by omega
  have selectedK : sk + (commonK - sk) = commonK := by omega
  rw [capturedR, capturedN, capturedK, completed] at capturedActual
  rw [selectedR, selectedN, selectedK] at selectedActual
  rcases selectedShape with ⟨selectedFragment, selectedDone, _selectedSafe, _fragmentBound, _rest⟩ |
    ⟨prefixFragments, outer, waiting, selectedStopped⟩
  · rw [selectedDone] at selectedActual
    have slotProtected := protects uv ready.inside ready.root (ready.avoids handle scs stored)
    have middleStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      slotProtected.value.trans stored
    cases finalized : SourcePruningEnumerationFinalize.run selectedCaller.checked.native.machine.heap
        commonK uv selectedFragment middle with
    | none =>
      simp only [run, selectedActual, finalized] at capturedActual
      cases capturedActual
    | some finished =>
      have returned : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete selectedFragment selectedCaller selectedQueries finished =
          SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete fragment afterCaller savedQueries after := by
        exact Option.some.inj (by simpa only [run, selectedActual, finalized] using capturedActual)
      have same : selectedFragment = fragment ∧ selectedCaller = afterCaller ∧
          selectedQueries = savedQueries ∧ finished = after := by
        simpa only [SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete.injEq] using returned
      obtain ⟨fragmentSame, _callerSame, _queriesSame, cacheSame⟩ := same
      have selectedCost :=
        SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.complete_pendingSize_le
          checkEmpty commonR commonN commonP commonH commonK scs edge caller selectedCaller
          before middle memos.query selectedQueries selectedFragment extended ready.safe.1.aligned selectedActual
      have finalizedCost := SourcePruningEnumerationStorageProgress.finalize_pendingSize
        selectedCaller.checked.native.machine.heap commonK uv handle selectedFragment scs
        middle finished extended middleStored finalized
      have originalCost : EnumerationStorageProgress.pendingSize before.core extended =
          EnumerationStorageProgress.pendingSize before.core assignment := by
        apply EnumerationStorageProgress.pendingSize_assignment_congr
        intro held inside
        apply agree held
        rw [ready.safe.1.aligned]
        exact inside
      rw [fragmentSame, filled, originalCost] at selectedCost
      rw [cacheSame] at finalizedCost
      omega
  · rw [selectedStopped] at selectedActual
    simp only [run, selectedActual] at capturedActual
    cases capturedActual

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
