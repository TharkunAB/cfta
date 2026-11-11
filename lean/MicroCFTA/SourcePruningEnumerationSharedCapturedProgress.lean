import MicroCFTA.SourcePruningEnumerationSharedCapturedEdgeModels
import MicroCFTA.SourcePruningEnumerationSharedSelectedProper
import MicroCFTA.SourcePruningEnumerationNativeProgress

/-!
# Local restart progress at the same shared captured model

The captured producer supplies one resource and semantic packet.
Current proper storage supplies proper paths at that same returned cache.
Its finite model excludes a stuck restart at that cache.
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

/-- The same completed captured packet has proper paths and a non-stuck restart. -/
theorem complete_models_resources_proper_progress_prepared
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
    (old : AssignmentOrigins whole before.core.counter assignment)
    (proper : EnumerationProgress.ProperState before.core) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      (((∀ er en P H ek, p ≤ P → h ≤ H →
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
        ∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
      EnumerationProgress.ProperState after.core ∧
      ∀ (Typing : Type)
        (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
        (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
        (metadata : SourcePruningRecordTypes.Metadata Typing),
        SourcePruningEnumerationRestart.decision stop order metadata after ≠ some .stuck := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, resource, model⟩ :=
    complete_models_resources_prepared seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored
      parentAvailable parentClosed realized selected paths counts flags pending tries residual
      projected fits reserved known ambient assignment whole satisfied accepted old
  have coupled := And.intro resource model
  rcases resource with ⟨stable, _post, _querySame, _growth, afterPaths, storage,
    afterRealized, afterCounts, afterFlags, _origin, _retained, _protects,
    _pendingHistory, shape, _returnedFits, _returnedKnown⟩
  rcases model with ⟨fragment, extended, completed, _extension, _inputModel, outputModel, _rest⟩
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      initial.ready.semantic.ready.semantic.1.normal.facts.linked
      (.node parentEntry edges depth free) parentAvailable.resident edge selected
  have cached := initial.annotation_heap edge.entry.key edge resident
  have actual : run checkEmpty r n p h k uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_zero] using stable 0 0 p h 0 (Nat.le_refl p) (Nat.le_refl h)
  have afterProper : EnumerationProgress.ProperState after.core := by
    have retained := observed_cache_proper checkEmpty r n p h k uv scs edge caller before
      memos.query proper stored cached actual
    simpa only [completed] using retained
  have valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid afterCaller after :=
    ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
  have afterSafe : Safe after.core := by
    rcases shape with ⟨_fragment, _completed, safe, _rest⟩ |
      ⟨_fragments, _outer, _waiting, stopped⟩
    · exact safe
    · rw [completed] at stopped
      cases stopped
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, coupled, afterProper, ?_⟩
  intro Typing stop order metadata
  exact SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver stop order metadata
    afterCaller after valid afterSafe afterProper ambient
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    extended outputModel

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
