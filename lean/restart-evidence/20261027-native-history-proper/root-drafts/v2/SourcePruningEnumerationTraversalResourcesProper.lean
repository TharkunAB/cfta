import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationTraversalEndpointProper

/-!
# Proper paths with the full original traversal resource packet

The same resource witnesses retain complete and rejected-prefix endpoints.
The proper-input observer follows the entire original packet.
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

/-- Retain every original traversal resource field and proper actual returned storage. -/
theorem complete_with_fragments_resources_proper
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
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
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
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap) ∧
      (EnumerationProgress.ProperState before.core →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → EnumerationProgress.ProperInputs bucket) →
        EnumerationProgress.ProperState after.core) := by
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before checkEmpty inputs
      roots memos initial safe paths counts flags realized genuine fits reserved known
  refine ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots, result, packet, ?_⟩
  intro proper inputsProper
  have actual := packet.1 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  have preserved := SourcePruningEnumerationChildTraversal.observed_cache_proper proper inputsProper actual
  obtain ⟨_running, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _enumeratedProtected, _rootsProtected,
    _references, _pending, _bounds, shape, _returnedFits, _returnedKnown⟩ := packet
  rcases shape with ⟨same, _safe, _fragments⟩ | ⟨outer, waiting, same⟩
  · subst result
    exact preserved
  · subst result
    exact preserved

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
