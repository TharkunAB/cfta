import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationCapturedEdgeScalarBounds

/-!
# Original scalar bounds for the full edge certificate

The original resource producer runs once. Its entire result remains available.
The same actual cache retains the original counter and suspended-mass bounds.
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

/-- Original resources retain the entire earlier edge certificate and bound its same returned cache. -/
theorem complete_with_history_cache_bounds
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
        afterCaller.checked.native.machine.heap ∧
      after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core +
          edge.children.length * (scs.length + tries.length) := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags, origin, retained, protects, pendingHistory, shape, afterFits, afterKnown⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
      selected paths counts flags pending allowed tries residual projected fits reserved known
  have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  have bounds := observed_scalar_bounds checkEmpty r n p h k uv scs edge caller before memos.query tries residual projected
  rw [actual] at bounds
  have scalars : after.core.counter ≤ before.core.counter + tries.length + edge.children.length ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core +
          edge.children.length * (scs.length + tries.length) := by
    rcases shape with ⟨fragment, completed, _safe, _bound, _written, _ancestry, _root, _pending, _ordered⟩ |
      ⟨fragments, outer, waiting, stopped⟩
    · simpa only [completed] using bounds
    · rw [stopped] at bounds
      exact bounds after rfl
  exact ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    result, observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags, origin, retained, protects, pendingHistory, shape, afterFits, afterKnown, scalars.1, scalars.2⟩

end MicroCFTA.SourcePruningEnumerationCapturedEdge
