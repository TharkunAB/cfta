import MicroCFTA.SourcePruningEnumerationSharedChildResources
import MicroCFTA.SourcePruningEnumerationSharedChildDispatchStability

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × Core))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A successful child observation retains the resources from the initial input. -/
theorem observed_complete_with_fragments_resources
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
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
    (savedQueries : Queries) (outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming beforeCaller before memos.query =
      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)]) :
    ∃ (final : Memos) (next : Inventory) (afterRoots : Nat → Nat),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
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
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap
 := by
  obtain ⟨r0, n0, p0, h0, k0, canonicalRaw, canonicalCaller, canonicalCache,
      canonicalQueries, final, next, afterRoots, canonicalOuter, canonicalWaiting, retained⟩ :=
    complete_with_fragments_resources seed formulas solver inventory beforeCaller before
      checkEmpty bucket incoming roots memos initial safe paths counts flags realized
      bounded pending available closed fits reserved known
  have observedLater := run_some_stable observed successful
    (Nat.le_add_right r r0) (Nat.le_add_right n n0) (Nat.le_add_right p p0)
    (Nat.le_add_right h h0) (Nat.le_add_right k k0)
  have canonicalLater := retained.1 r n (p + p0) (h + h0) k (by omega) (by omega)
  rw [Nat.add_comm r0 r, Nat.add_comm n0 n, Nat.add_comm k0 k] at canonicalLater
  have comparison := observedLater.symm.trans canonicalLater
  have same :
      (raw = canonicalRaw ∧ afterCaller = canonicalCaller ∧
        savedQueries = canonicalQueries ∧ outer = canonicalOuter ∧ waiting = canonicalWaiting) ∧
      after = canonicalCache := by
    simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] using comparison
  obtain ⟨⟨rawSame, callerSame, queriesSame, outerSame, waitingSame⟩, cacheSame⟩ := same
  subst canonicalRaw canonicalCaller canonicalQueries canonicalOuter canonicalWaiting canonicalCache
  refine ⟨final, next, afterRoots, ?_, retained.2⟩
  intro extraRepresentative extraNative P H extraIndex enoughP enoughH
  exact run_some_stable observed successful
    (Nat.le_add_right r extraRepresentative) (Nat.le_add_right n extraNative)
    enoughP enoughH (Nat.le_add_right k extraIndex)

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
