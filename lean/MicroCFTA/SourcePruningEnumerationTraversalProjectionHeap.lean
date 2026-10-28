import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationChildDispatchUnique
import MicroCFTA.SourcePruningEnumerationChildProjectionHeap

/-!
# Actual next entries for ordered child traversal

The original child producer supplies its full returned native context.
Successful point uniqueness attaches that context to the actual singleton.
The original suffix inputs and projection heap remain admitted there.
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
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {bits : Nat}

/-- An actual singleton derives the next original traversal admissions and projection heap. -/
theorem observed_singleton_resources_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (incoming : Node) (bucket : List Suspended)
    (rest : List (Node × List Suspended)) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ value retained, (value, retained) ∈ (incoming, bucket) :: rest →
      Available beforeCaller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost ((incoming, bucket) :: rest)))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {r n p h k : Nat} {fragment : Fragment} {returned : Core}
    {afterCaller : Caller (bits + 2)} {after : Cached} {savedQueries : Queries}
    {outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (observed : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
      bucket incoming beforeCaller before memos.query =
        ((.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, waiting), some after)) :
    ∃ (next : Inventory) (final : Memos) (afterRoots : Nat → Nat),
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Safe after.core ∧ Roots after.core.representatives afterRoots ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      (∀ value retained, (value, retained) ∈ rest →
        Available afterCaller.checked.native.machine.heap value ∧ value.free = [] ∧
        (∀ sc ∈ retained, sc.var < after.core.counter) ∧ InputsPending after.core retained) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1)
        afterCaller.checked.native.machine.heap ∧
      Reserved bits (advance seed (bucket.length + 1)) (cost rest) ∧
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
  have headReservation : Reserved bits seed (bucket.length + 1) :=
    reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)
  have current := SourcePruningEnumerationChildDispatch.observed_resources_projection_heap
    seed formulas solver inventory beforeCaller before checkEmpty r n p h k bucket incoming roots memos
    initial safe paths counts realized bounded pending available closed fits headReservation known
    originalProjection observed
  obtain ⟨headR, headN, headP, headH, headK, raw, producedCaller, produced, producedQueries,
    final, next, afterRoots, _producedOuter, _producedWaiting, stable, post, querySame, growth,
    afterPaths, _storage, afterRealized, afterCounts, afterFlags, origin, protectsRoots,
    _references, _pendingHistory, shape, _producedFits, _producedKnown⟩ :=
    SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed formulas solver inventory
      beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts flags realized
      bounded pending available closed fits headReservation known
  have producedObservation := stable 0 0 headP headH 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at producedObservation
  have supported : raw = [] ∨ ∃ child returned, raw = [.ok (child, returned)] := by
    rcases shape with rejected | ⟨child, singleton, _safe, _bound, _pending, _separate⟩
    · exact .inl rejected
    · exact .inr ⟨child, produced.core, singleton⟩
  obtain ⟨rawSame, callerSame, queriesSame, _outerSame, _waitingSame, cacheSame⟩ :=
    SourcePruningEnumerationChildDispatch.run_some_unique observed (.inr ⟨fragment, returned, rfl⟩)
      producedObservation supported
  subst producedCaller
  cases queriesSame
  subst produced
  have afterSafe : Safe after.core := by
    rcases shape with rejected | ⟨_child, _singleton, admitted, _bound, _pending, _separate⟩
    · rw [rejected] at rawSame
      cases rawSame
    · exact admitted
  have protects : ∀ held child, before.core.values[held]? = some (.enumerated child) →
      EnumerationDriver.Protected held before.core after.core := by
    intro held child stored
    obtain ⟨inside, root⟩ := enumerated_root before.core safe held child stored
    exact protectsRoots held inside root (pending held child stored)
  have tailGenuine : ∀ value retained, (value, retained) ∈ rest →
      Available afterCaller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ sc ∈ retained, sc.var < after.core.counter) ∧ InputsPending after.core retained := by
    intro value retained member
    obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
      genuine value retained (List.mem_cons_of_mem _ member)
    refine ⟨post.effects.keeps.available value childAvailable, childClosed,
      fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
    intro held child stored
    have old := origin held child stored
    exact (protects held child old).avoids retained (childPending held child old)
  exact ⟨next, final, afterRoots, post, querySame, afterSafe, afterPaths, afterCounts,
    afterFlags, afterRealized, tailGenuine, current.1, current.2.1, reserved.after_prefix, current.2.2⟩

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
