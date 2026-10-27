import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourceFlatPruningChildResources
import MicroCFTA.SourceFlatPruningChildTraversal

/-!
# Actual flat traversal from original child resources

Each reached child supplies the next actual caller and cache.
The original buckets determine the complete mixed reservation.
Rejection retains its native effects and does not run the remaining children.
-/
namespace MicroCFTA.SourceFlatPruningTraversalResources
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

open SourcePruningEnumerationTraversalCompletion (cost)

/-- A related successful singleton retains its value and its actual returned state. -/
private theorem singleton_related
    {Left Right Error Value : Type} {relation : Left → Right → Prop}
    {rows : List (Except Error (Value × Left))} {value : Value} {right : Right}
    (related : EnumerationResultRelation.Results relation rows [.ok (value, right)]) :
    ∃ left, rows = [.ok (value, left)] ∧ relation left right := by
  cases related with
  | cons head tail =>
    cases tail
    cases head with
    | ok _ states => exact ⟨_, rfl, states⟩

/-- Original resources retain the full traversal packet and its actual returned caller. -/
theorem complete_with_fragments_resources
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
      (∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
        EnumerationFlatCached.Related flat before →
        ∀ extraNative P H, p ≤ P → h ≤ H →
          ∃ flatResult : SourceFlatPruningChildTraversal.Result (bits + 2),
            SourceFlatPruningChildTraversal.run checkEmpty (n + extraNative) P H
              inputs beforeCaller flat memos.query = flatResult ∧
            SourceFlatPruningChildTraversal.ResultRelated flatResult result) := by
  induction inputs generalizing seed inventory beforeCaller before roots memos with
  | nil =>
      refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
        .complete [] beforeCaller memos.query before, ?_, Post.refl initial, rfl, Nat.le_refl _,
        paths, safe.1, realized, counts, flags, .refl _, ?_, ?_, (fun _ valid _ => valid),
        (fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩
      · intros; rfl
      · intro held fragment stored
        exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core safe held fragment stored).2
      · intro held _ root _
        exact EnumerationDriver.Protected.refl held before.core root
      · simp
      · intro flat related _extraNative _P _H _largeP _largeH
        exact ⟨.complete [] beforeCaller memos.query flat, rfl, ⟨rfl, rfl, rfl, related⟩⟩
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      obtain ⟨r, n, p, h, k, raw, middleCaller, middle, middleQueries, middleMemos, middleInventory,
        middleRoots, outer, waiting, headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape, middleFits, middleKnown, headFlat⟩ :=
        SourceFlatPruningChildResources.complete_with_fragments_resources seed formulas solver inventory beforeCaller before
          checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending available closed fits
          (reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)) known
      have protects : ∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
          EnumerationDriver.Protected held before.core middle.core := by
        intro held fragment stored
        obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment stored
        exact headProtected held inside root (pending held fragment stored)
      rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩
      · subst raw
        refine ⟨r, n, p, h, k, [], middleCaller, middle, middleQueries, middleMemos, middleInventory,
          middleRoots, .stopped [] (.ok (some []), middleCaller, middleQueries, outer, waiting) (some middle),
          ?_, headPost, headQueries, growth, middlePaths, middleStorage, middleRealized, middleCounts,
          middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationChildTraversal.run, headRun er en P H ek largeP largeH]
        · intro held inside root avoids
          exact headProtected held inside root (avoids incoming bucket (by simp))
        · intro allowed valid allowedInputs
          exact headReferences allowed valid (allowedInputs incoming bucket (by simp))
        · simp
        · change Fits (advance seed ((bucket.length + 1) + cost rest)).2 middleCaller.checked
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact middleFits.mono
            (SourcePruningEnumerationIncomingReservation.advance_profile_ge (advance seed (bucket.length + 1)) (cost rest))
        · change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            middleCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          intro key edge found
          exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
            (advance seed (bucket.length + 1)) (cost rest) (middleKnown key edge found)
        · intro flat related en P H largeP largeH
          obtain ⟨flatRows, flatOuter, recovered, flatHead, cacheRelated, outerRelated,
            rawRelated, _correct⟩ := headFlat flat related en P H largeP largeH
          cases rawRelated
          let flatResult : SourceFlatPruningChildTraversal.Result (bits + 2) :=
            .stopped [] (.ok (some []), middleCaller, middleQueries, flatOuter, waiting) (some recovered)
          refine ⟨flatResult, ?_, ?_⟩
          · simp only [SourceFlatPruningChildTraversal.run, flatHead, flatResult]
          · exact ⟨rfl, ⟨⟨rfl, rfl, outerRelated, rfl, .nil⟩, cacheRelated⟩⟩
      · have tailGenuine : ∀ value bucket, (value, bucket) ∈ rest →
            Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
            (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value retained member
          obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
            genuine value retained (List.mem_cons_of_mem _ member)
          refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
            fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
          intro held storedFragment stored
          have old := headOrigin held storedFragment stored
          exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
        have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
          reserved.after_prefix
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailFlat⟩ :=
          ih (advance seed (bucket.length + 1)) middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe
            middlePaths middleCounts middleFlags middleRealized tailGenuine middleFits tailReservation middleKnown
        have finalFits : Fits (advance seed (cost ((incoming, bucket) :: rest))).2 afterCaller.checked := by
          change Fits (advance seed ((bucket.length + 1) + cost rest)).2 afterCaller.checked
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact tailFits
        have finalKnown : Heap (fun guard => guard ∈ (advance seed (cost ((incoming, bucket) :: rest))).1)
            afterCaller.checked.native.machine.heap := by
          change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            afterCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact tailKnown
        let result : SourcePruningEnumerationChildTraversal.Result (bits + 2) := match tailResult with
          | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
          | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
        refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
          fragment :: tailFragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, headOrigin.trans tailOrigin, ?_, ?_, ?_,
          (fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown, ?_⟩
        · intro er en P H ek largeP largeH
          have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have tail := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have headExact : SourcePruningEnumerationChildDispatch.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
            simpa only [Nat.add_assoc, singleton] using head
          have tailExact : SourcePruningEnumerationChildTraversal.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) rest middleCaller middle middleQueries = tailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
          simp only [SourcePruningEnumerationChildTraversal.run, headExact, tailExact, result]
          cases tailResult <;> rfl
        · intro held storedFragment stored
          have first := protects held storedFragment stored
          have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
          exact first.trans (tailProtected held storedFragment middleStored)
        · intro held inside root avoids
          have first := headProtected held inside root (avoids incoming bucket (by simp))
          apply first.trans
          apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
          intro value retained member
          exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
        · intro allowed valid allowedInputs
          apply tailReferences allowed
            (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
          intro value retained member
          exact allowedInputs value retained (List.mem_cons_of_mem _ member)
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
          · exact tailBounds child member
        · rcases tailShape with ⟨completed, afterSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
          · subst tailResult
            refine .inl ⟨rfl, afterSafe, ?_⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨pendingFragment_preserved middle.core after.core middleSafe afterSafe tailGrowth
                child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
                intro value retained member
                exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member)))
              exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
                last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
            · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
              refine ⟨childPending, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
              intro value retained member
              exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
          · subst tailResult
            exact .inr ⟨outer, waiting, rfl⟩

        · intro flat related en P H largeP largeH
          obtain ⟨flatRows, flatOuter, middleFlat, flatHead, middleRelated, _outerRelated,
            rawRelated, _correct⟩ :=
            headFlat flat related (tailN + en) P H
              (Nat.le_trans (Nat.le_max_left _ _) largeP)
              (Nat.le_trans (Nat.le_max_left _ _) largeH)
          rw [singleton] at rawRelated
          obtain ⟨returned, rowsSame, _returnedRelated⟩ := singleton_related rawRelated
          rw [rowsSame] at flatHead
          obtain ⟨flatTailResult, flatTail, tailRelated⟩ :=
            tailFlat middleFlat middleRelated (n + en) P H
              (Nat.le_trans (Nat.le_max_right _ _) largeP)
              (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have flatHeadExact : SourceFlatPruningChildDispatch.run checkEmpty
              ((n + tailN) + en) P H bucket incoming beforeCaller flat memos.query =
              ((.ok (some [.ok (fragment, returned)]), middleCaller, middleQueries,
                flatOuter, waiting), some middleFlat) := by
            simpa only [Nat.add_assoc] using flatHead
          have flatTailExact : SourceFlatPruningChildTraversal.run checkEmpty
              ((n + tailN) + en) P H rest middleCaller middleFlat middleQueries = flatTailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using flatTail
          let flatResult : SourceFlatPruningChildTraversal.Result (bits + 2) := match flatTailResult with
            | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
            | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
          refine ⟨flatResult, ?_, ?_⟩
          · simp only [SourceFlatPruningChildTraversal.run, flatHeadExact, flatTailExact, flatResult]
            cases flatTailResult <;> rfl
          · cases tailResult with
            | complete fragments caller queries cache =>
              cases flatTailResult with
              | complete flatFragments flatCaller flatQueries flatCache =>
                obtain ⟨fragmentsSame, callerSame, queriesSame, cacheRelated⟩ := tailRelated
                exact ⟨congrArg (List.cons fragment) fragmentsSame, callerSame, queriesSame, cacheRelated⟩
              | stopped flatFragments observation candidate => exact False.elim tailRelated
            | stopped fragments observation candidate =>
              cases flatTailResult with
              | complete flatFragments flatCaller flatQueries flatCache => exact False.elim tailRelated
              | stopped flatFragments flatObservation flatCandidate =>
                obtain ⟨fragmentsSame, observationRelated⟩ := tailRelated
                exact ⟨congrArg (List.cons fragment) fragmentsSame, observationRelated⟩


end MicroCFTA.SourceFlatPruningTraversalResources
