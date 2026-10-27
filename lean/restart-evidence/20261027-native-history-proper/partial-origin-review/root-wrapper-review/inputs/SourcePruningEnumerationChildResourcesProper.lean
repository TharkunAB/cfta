import MicroCFTA.SourcePruningEnumerationChildResources
import MicroCFTA.SourcePruningEnumerationChildProper

/-!
# Proper paths with the full original child resource packet

The original bounds and returned packet precede the proper-input observer.
The actual attached cache remains covered on rejection.
-/
namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the entire original child resource packet and its proper attached cache. -/
theorem complete_with_fragments_resources_proper
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap) ∧
      (EnumerationProgress.ProperState before.core → EnumerationProgress.ProperInputs bucket →
        EnumerationProgress.ProperState after.core) := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, packet⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before checkEmpty bucket incoming
      roots memos initial safe paths counts flags realized bounded pending available closed fits reserved known
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, packet, ?_⟩
  intro proper inputs
  have actual := packet.1 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  apply SourcePruningEnumerationChildDispatch.observed_cache_proper checkEmpty r n p h k bucket incoming
    beforeCaller before memos.query proper inputs after
  simpa only [Nat.add_zero] using congrArg Prod.snd actual

end MicroCFTA.SourcePruningEnumerationChildCompletion
