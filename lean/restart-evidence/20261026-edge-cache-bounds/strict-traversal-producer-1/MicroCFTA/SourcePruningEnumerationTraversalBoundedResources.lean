import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationTraversalScalarBounds

/-!
# Original scalar bounds for complete traversal packets

The original traversal producer runs once. Its entire result remains available.
The same actual complete or rejected cache retains the original scalar bounds.
-/
namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion
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
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

/-- Original resources retain the full traversal packet and add scalar bounds on its same cache. -/
theorem complete_with_fragments_cache_bounds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result (bits + 2)),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) inputs beforeCaller before memos.query = result) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
      ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core ∧
          ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
            ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
              (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
              FragmentAvoid after.core.representatives held fragment) ∨
        ∃ outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      after.core.counter ≤ before.core.counter + inputs.length ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core +
          (inputs.map fun input => input.2.length).sum := by
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    result, observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
    afterFlags, origin, protected, rootsProtected, references, pendingHistory, fragmentBounds,
    shape, afterFits, afterKnown⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before checkEmpty inputs
      roots memos initial safe paths counts flags realized genuine fits reserved known
  have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  have bounds := SourcePruningEnumerationChildTraversal.observed_scalar_bounds
    checkEmpty r n p h k inputs beforeCaller before memos.query
  rw [actual] at bounds
  have scalars : after.core.counter ≤ before.core.counter + inputs.length ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core +
          (inputs.map fun input => input.2.length).sum := by
    rcases shape with ⟨completed, _safe, _fragments⟩ | ⟨outer, waiting, stopped⟩
    · simpa only [completed] using bounds
    · rw [stopped] at bounds
      exact bounds after rfl
  exact ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    result, observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
    afterFlags, origin, protected, rootsProtected, references, pendingHistory, fragmentBounds,
    shape, afterFits, afterKnown, scalars.1, scalars.2⟩

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
