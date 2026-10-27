import MicroCFTA.SourcePruningEnumerationCapturedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationCapturedEdgeProper
import MicroCFTA.SourcePruningEnumerationNativeProgress

/-!
# Native scheduler progress at the actual accepted captured endpoint

The full original resource and coverage packet remains available.
An original proper model derives proper storage at the same completed cache.
The same constructed model excludes stuck selection at that endpoint.
No later callback or recursive execution is an input.
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

/-- Keep the complete accepting packet and derive proper native restart at its actual accepted endpoint. -/
theorem complete_with_history_resources_progress
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
        afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          result = .complete fragment afterCaller savedQueries after ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended after.core) ∧
      EnumerationProgress.ProperState before.core →
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          result = .complete fragment afterCaller savedQueries after ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended after.core ∧
          EnumerationProgress.ProperState after.core ∧
          ∀ (Typing : Type)
            (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
            (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
            (metadata : SourcePruningRecordTypes.Metadata Typing),
            SourcePruningEnumerationRestart.decision stop order metadata after ≠ some .stuck := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, retained, protects, pendingHistory, shape, returnedFits, returnedKnown, accepting⟩ :=
    complete_with_history_resources_accepting seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
      selected paths counts flags pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    ⟨running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
      origin, retained, protects, pendingHistory, shape, returnedFits, returnedKnown, accepting⟩, ?_⟩
  intro proper ambient assignment satisfied accepted
  obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
    accepting ambient assignment satisfied accepted
  have actual : run checkEmpty r n p h k uv scs edge caller before memos.query =
      some (.complete fragment afterCaller savedQueries after) := by
    have observed := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    simpa only [Nat.add_zero, completed] using observed
  have afterProper := complete_proper formulas solver inventory caller before checkEmpty
    uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
    selected paths counts flags pending allowed tries residual projected proper actual
  have afterSafe : Safe after.core := by
    rcases shape with ⟨produced, same, safe, rest⟩ | ⟨fragments, outer, waiting, stopped⟩
    · exact safe
    · rw [completed] at stopped
      cases stopped
  have afterValid : SourcePruningEnumerationNativeBranchCompletion.CacheValid afterCaller after :=
    ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
  refine ⟨extended, fragment, agree, originalSatisfied, completed, filled, afterSatisfied, afterProper, ?_⟩
  intro Typing stop order metadata
  exact SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver stop order metadata
    afterCaller after afterValid afterSafe afterProper ambient
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
    extended afterSatisfied

end MicroCFTA.SourcePruningEnumerationCapturedEdge
