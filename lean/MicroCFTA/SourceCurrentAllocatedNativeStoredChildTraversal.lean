import MicroCFTA.SourceCurrentAllocatedNativeStoredChildDispatch
import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationChildDispatchUnique

/-!
# Native structural certificates at every actual child traversal outcome

Actual singleton child observations derive the current recursive entry facts.
Every stopped result retains the reached caller's native certificates.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredChildTraversal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationTraversalCompletion (cost)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

/-- Every actual traversal outcome retains native certificates under its current reservation. -/
theorem child_traversal_native_stored
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
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
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native) :
    match SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k inputs
      beforeCaller before memos.query with
    | .complete _ caller _ _ => Stored caller.checked.native
    | .stopped _ observation _ => Stored observation.2.1.checked.native := by
  induction inputs generalizing seed inventory beforeCaller before roots memos with
  | nil => exact stored
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      have headReservation : Reserved bits seed (bucket.length + 1) :=
        reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)
      have headStored := SourceCurrentAllocatedNativeStoredChildDispatch.child_dispatch_native_stored
        seed formulas solver inventory beforeCaller before checkEmpty r n p h k bucket incoming
        roots memos initial safe paths counts realized bounded pending available closed fits
        headReservation known stored
      rcases headObserved : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
          bucket incoming beforeCaller before memos.query with
        ⟨⟨outcome, middleCaller, middleQueries, outer, waiting⟩, candidate⟩
      rw [headObserved] at headStored
      change Stored middleCaller.checked.native at headStored
      rw [SourcePruningEnumerationChildTraversal.run, headObserved]
      cases outcome with
      | error fault => exact headStored
      | ok possible =>
        cases possible with
        | none => exact headStored
        | some raw =>
          cases raw with
          | nil => exact headStored
          | cons entry tail =>
            cases entry with
            | error fault => exact headStored
            | ok row =>
              rcases row with ⟨fragment, returned⟩
              cases tail with
              | cons second remaining => exact headStored
              | nil =>
                cases candidate with
                | none => exact headStored
                | some middle =>
                  obtain ⟨lowR, lowN, lowP, lowH, lowK, canonicalRaw, canonicalCaller,
                    canonicalCache, canonicalQueries, final, next, middleRoots, canonicalOuter,
                    canonicalWaiting, stable, post, querySame, growth, middlePaths, _middleStorage,
                    middleRealized, middleCounts, middleFlags, origin, protects, _references,
                    _pendingHistory, shape, middleFits, middleKnown⟩ :=
                    SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed
                      formulas solver inventory beforeCaller before checkEmpty bucket incoming
                      roots memos initial safe paths counts flags realized bounded pending
                      available closed fits headReservation known
                  have canonical := stable 0 0 lowP lowH 0 (Nat.le_refl _) (Nat.le_refl _)
                  simp only [Nat.add_zero] at canonical
                  have supported : canonicalRaw = [] ∨ ∃ child actualCore,
                      canonicalRaw = [.ok (child, actualCore)] := by
                    rcases shape with rejected | ⟨child, singleton, _safe, _bound, _pending, _avoids⟩
                    · exact .inl rejected
                    · exact .inr ⟨child, canonicalCache.core, singleton⟩
                  obtain ⟨rawSame, callerSame, queriesSame, _outerSame, _waitingSame, cacheSame⟩ :=
                    SourcePruningEnumerationChildDispatch.run_some_unique canonical supported
                      headObserved (.inr ⟨fragment, returned, rfl⟩)
                  subst canonicalCaller
                  subst canonicalCache
                  rw [queriesSame] at querySame
                  rcases shape with rejected | ⟨_child, _singleton, middleSafe, _bound, _pending, _avoids⟩
                  · rw [rejected] at rawSame
                    cases rawSame
                  · have priorProtected : ∀ held oldFragment,
                        before.core.values[held]? = some (.enumerated oldFragment) →
                        EnumerationDriver.Protected held before.core middle.core := by
                      intro held oldFragment old
                      obtain ⟨inside, root⟩ := enumerated_root before.core safe held oldFragment old
                      exact protects held inside root (pending held oldFragment old)
                    have tailGenuine : ∀ value retained, (value, retained) ∈ rest →
                        Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
                        (∀ sc ∈ retained, sc.var < middle.core.counter) ∧ InputsPending middle.core retained := by
                      intro value retained member
                      obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
                        genuine value retained (List.mem_cons_of_mem _ member)
                      refine ⟨post.effects.keeps.available value childAvailable, childClosed,
                        fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
                      intro held oldFragment old
                      have prior := origin held oldFragment old
                      exact (priorProtected held oldFragment prior).avoids retained (childPending held oldFragment prior)
                    have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
                      reserved.after_prefix
                    have tailStored := ih (advance seed (bucket.length + 1)) next middleCaller middle
                      middleRoots final post.context middleSafe middlePaths middleCounts middleFlags
                      middleRealized tailGenuine middleFits tailReservation middleKnown headStored
                    rw [querySame] at tailStored
                    cases tailObserved : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                        rest middleCaller middle middleQueries with
                    | complete fragments finalCaller finalQueries finalCache =>
                        simpa only [tailObserved] using tailStored
                    | stopped _processed observation after =>
                        simpa only [tailObserved] using tailStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredChildTraversal
