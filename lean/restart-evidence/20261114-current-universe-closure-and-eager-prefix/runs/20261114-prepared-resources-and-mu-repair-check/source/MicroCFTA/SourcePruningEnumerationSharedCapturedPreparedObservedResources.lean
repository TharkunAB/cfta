import MicroCFTA.SourcePruningEnumerationSharedCapturedPreparedResources
import MicroCFTA.SourcePruningEnumerationSharedSelectedEdgeStability

/-!
# Full original resources at an observed completed actual prepared row

The current receipt is compared with the original producer at common bounds.
All original initial premises and resource fields remain in the interface.
No future receipt or callback resource is an input premise.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual completed prepared row supplies every original captured-row resource. -/
theorem observed_complete_with_history_resources_prepared
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
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (rNow nNow pNow hNow kNow : Nat) (observedFragment : Fragment)
    (observedCaller : Caller (bits + 2)) (observedQueries : Queries) (observedCache : Cached)
    (observed : run checkEmpty rNow nNow pNow hNow kNow uv scs edge caller before memos.query =
      some (.complete observedFragment observedCaller observedQueries observedCache)) :
    ∃ (r n p h k : Nat) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete observedFragment observedCaller observedQueries observedCache)) ∧
      Post formulas solver next caller observedCaller final ∧ final.query = observedQueries ∧
      before.core.counter ≤ observedCache.core.counter ∧ Roots observedCache.core.representatives afterRoots ∧
      StorageValid observedCache.core ∧ PendingRealized observedCaller.checked.native.machine.heap observedCache.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots observedCache.core.values observedCache.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate observedCaller.checked.native.machine.heap
        ((observedCache.core.values[slot]?).getD .eliminated) = some (observedCache.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → observedCache.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending observedCache.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core observedCache.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences observedCache.core) ∧
      ((∃ fragment, (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete observedFragment observedCaller observedQueries observedCache) = .complete fragment observedCaller observedQueries observedCache ∧
          Safe observedCache.core ∧ FragmentBound observedCache.core.counter fragment ∧
          observedCache.core.values[uv]? = some (.enumerated fragment) ∧ observedCache.core.expansionAncestry = [] ∧
          IsRoot observedCache.core.representatives uv ∧ PendingFragment observedCache.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified observedCache.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete observedFragment observedCaller observedQueries observedCache) = .stopped fragments
          (.ok (some []), observedCaller, observedQueries, outer, waiting) (some observedCache)) ∧
      Fits (advance seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).2 observedCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).1)
        observedCaller.checked.native.machine.heap := by
  obtain ⟨r, n, p, h, k, canonicalCaller, canonicalCache, canonicalQueries,
      final, next, afterRoots, canonicalReceipt, retained⟩ :=
    complete_with_history_resources_prepared seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored
      parentAvailable parentClosed realized selected paths counts flags pending allowed tries residual
      projected fits reserved known
  let common : Nat := r + n + p + h + k + rNow + nNow + pNow + hNow + kNow
  have observedLater := complete_stable
    (R := common) (N := common) (P := common) (H := common) (K := common)
    observed (by dsimp [common]; omega) (by dsimp [common]; omega)
      (by dsimp [common]; omega) (by dsimp [common]; omega) (by dsimp [common]; omega)
  have canonicalLater := retained.1 (common - r) (common - n) common common (common - k)
    (by dsimp [common]; omega) (by dsimp [common]; omega)
  have sameR : r + (common - r) = common := by dsimp [common]; omega
  have sameN : n + (common - n) = common := by dsimp [common]; omega
  have sameK : k + (common - k) = common := by dsimp [common]; omega
  rw [sameR, sameN, sameK] at canonicalLater
  have sameReceipt : canonicalReceipt =
      SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete
        observedFragment observedCaller observedQueries observedCache :=
    Option.some.inj (canonicalLater.symm.trans observedLater)
  subst canonicalReceipt
  have currentShape := retained.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases currentShape with ⟨produced, producedEq, _remaining⟩ | ⟨fragments, outer, waiting, stopped⟩
  · obtain ⟨_sameFragment, sameCaller, sameQueries, sameCache⟩ :=
      SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete.inj producedEq
    subst canonicalCaller canonicalQueries canonicalCache
    exact ⟨r, n, p, h, k, final, next, afterRoots, retained⟩
  · cases stopped

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge

#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.observed_complete_with_history_resources_prepared
