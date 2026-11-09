import MicroCFTA.SourcePruningEnumerationSharedFoldCompletion
import MicroCFTA.SourcePruningEnumerationCachedAssimilation

/-!
# Cached fold completion through the shared dispatcher

The actual shared dispatcher supplies each head return and its full Post.
Pure cache writes derive current storage, waiting counts and candidate
flags. The literal cached fold then continues from that same caller,
query memo and cache. No old dispatcher or fold execution is reused.

The component proof takes the shared range predicate. The resource
companion derives it from current facts and the original shared reservation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

private theorem cachedDispatch_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (source target : Nat) (memos : Memos) (roots : Nat → Nat)
    (initial : Context formulas solver inventory beforeCaller memos)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (slots : source = target ∨ before.core.values[source]? = some .eliminated ∨
      ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
        before.core.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (ranges : if source = target then True else
      match before.core.values[source]?, before.core.values[target]? with
      | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap left,
              lookupNode beforeCaller.checked.native.machine.heap right with
          | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
              beforeCaller.checked
          | _, _ => True
      | _, _ => True) :
    ∃ (fuel p h : Nat) (action : EnumerateM Symbol Constraint Unit)
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedDispatch.dispatch checkEmpty (fuel + extra) P H
          beforeCaller before.core source target memos.query =
          (.ok (some action), afterCaller, savedQueries)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      ExceptT.run (action before.core) = rows.map (fun row => .ok (row.1, row.2.core)) ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      ((source = target ∨ before.core.values[source]? = some .eliminated) →
        rows = [((), before)] ∧ after = before ∧
        afterCaller = beforeCaller ∧ final = memos ∧ next = inventory) ∧
      (source ≠ target → before.core.values[source]? ≠ some .eliminated →
        ∃ (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
          before.core.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
          before.core.values[target]? = some (.unenumerated targetNode targetScs) ∧
          (∀ (cacheFuel : Nat), SourcePruningEnumerationCachedAssimilation.finish
            afterCaller.checked.native.machine.heap cacheFuel source target merged sourceScs targetScs before =
              some (rows, after)) ∧
          (if merged = some 0 then rows = [] ∧ after = before else
            rows = [((), after)] ∧
            after.core = assimilated before.core target source (.unenumerated merged (sourceScs ++ targetScs)) ∧
            after.core.values[source]? = some .eliminated ∧
            after.core.values[target]? = some (.unenumerated merged (sourceScs ++ targetScs)) ∧
            after.expandable source = false ∧
            (∀ (slot : Nat), slot ≠ source → slot ≠ target → after.expandable slot = before.expandable slot))) := by
  obtain ⟨fuel, p, h, action, afterCaller, savedQueries, final, next,
    actual, post, savedSame, heapRealized, noOpResult, liveResult⟩ :=
      SourcePruningEnumerationSharedDispatch.dispatch_complete formulas solver inventory beforeCaller
        before.core checkEmpty source target memos initial realized slots ranges
  have grownFlags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
    intro slot
    specialize flags slot
    generalize slotValueSame : ((before.core.values[slot]?).getD .eliminated) = slotValue at flags ⊢
    clear slotValueSame
    cases slotValue with
    | enumerated _oldEnumerated => exact flags
    | eliminated => exact flags
    | unenumerated oldNode oldScs =>
      cases oldNode with
      | none => exact flags
      | some oldHandle =>
        cases oldLookup : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
        | none =>
          simp only [SourcePruningEnumerationNativeIndex.candidate, oldLookup, Option.map_none] at flags
          cases flags
        | some oldValue =>
          simpa only [SourcePruningEnumerationNativeIndex.candidate, oldLookup,
            lookupNode_keeps beforeCaller.checked.native.machine.heap afterCaller.checked.native.machine.heap
              post.effects.keeps oldHandle oldValue oldLookup, Option.map_some] using flags
  by_cases noOp : source = target ∨ before.core.values[source]? = some .eliminated
  · obtain ⟨rawNoop, callerSame, finalSame, nextSame⟩ := noOpResult noOp
    refine ⟨fuel, p, h, action, afterCaller, savedQueries, final, next, [((), before)], before,
      actual, post, savedSame, rawNoop, rfl, rfl, paths, storage, heapRealized,
      counts, rfl, grownFlags, ?_, ?_⟩
    · intro _again
      exact ⟨rfl, rfl, callerSame, finalSame, nextSame⟩
    · intro unequal live
      exact False.elim (noOp.elim unequal live)
  ·
    have different : source ≠ target := by
      exact fun sameId => noOp (Or.inl sameId)
    have sourceLive : before.core.values[source]? ≠ some .eliminated := by
      exact fun eliminatedSource => noOp (Or.inr eliminatedSource)
    obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
      rawSelected, _selectedResult, optionalOrigin, queriedOrigin⟩ := liveResult different sourceLive
    have mergedRealized : ∀ (handle : Nat), merged = some handle →
        ∃ (value : Node), lookupNode afterCaller.checked.native.machine.heap handle = some value ∧
          Available afterCaller.checked.native.machine.heap value ∧ value.free = [] := by
      intro handle chosen
      cases sourceNode with
      | none =>
        obtain ⟨mergedSame, _optionalCaller, _optionalFinal, _optionalNext⟩ := optionalOrigin (Or.inl rfl)
        cases targetNode with
        | none =>
          rw [mergedSame] at chosen
          change none = some handle at chosen
          cases chosen
        | some rightHandle =>
          cases Option.some.inj (mergedSame.symm.trans chosen)
          exact heapRealized target _ targetScs targetStored
      | some leftHandle =>
        cases targetNode with
        | none =>
          obtain ⟨mergedSame, _optionalCaller, _optionalFinal, _optionalNext⟩ := optionalOrigin (Or.inr rfl)
          cases Option.some.inj (mergedSame.symm.trans chosen)
          exact heapRealized source _ sourceScs sourceStored
        | some rightHandle =>
          obtain ⟨_left, _right, _query, replacement, _queried, _returnedHandle,
            _leftLookup, _rightLookup, _nextSource, _nextRoots, _receipt, mergedSame,
            _encoded, decoded, available, closed, _meaning, _disabled, _enabled⟩ :=
              queriedOrigin leftHandle rightHandle rfl rfl
          cases Option.some.inj (mergedSame.symm.trans chosen)
          exact ⟨replacement, decoded, available, closed⟩
    obtain ⟨rows, after, computed, rawCached, counterSame, forestSame, afterPaths, afterStorage,
      cacheRealized, afterCounts, waitingSame, afterFlags, result⟩ :=
        SourcePruningEnumerationCachedAssimilation.complete afterCaller.checked.native.machine.heap
          before source target sourceNode targetNode merged sourceScs targetScs roots
          storage heapRealized paths counts grownFlags sourceStored targetStored (Ne.symm different) mergedRealized
    refine ⟨fuel, p, h, action, afterCaller, savedQueries, final, next, rows, after,
      actual, post, savedSame, ?_, counterSame, forestSame, afterPaths, afterStorage,
      cacheRealized, afterCounts, waitingSame, afterFlags, ?_, ?_⟩
    · rw [rawSelected]
      exact rawCached
    · intro impossibleNoOp
      exact False.elim (noOp impossibleNoOp)
    · intro _unequal _live
      exact ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
        computed, result⟩


/-- Derive common finite bounds and a valid cache for the admitted ordered fold. -/
theorem cachedFold_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos) (roots : Nat → Nat)
    (initial : Context formulas solver inventory beforeCaller memos)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (ranges : Ranges checkEmpty sources
      beforeCaller before.core target memos.query) :
    ∃ (fuel p h : Nat)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra P H, p ≤ P → h ≤ H →
        fold checkEmpty (fuel + extra) P H sources
          beforeCaller before target memos.query =
          ((.ok (some (rows.map (fun row => .ok (row.1, row.2.core)))),
            afterCaller, savedQueries, after.core), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (rows = [] ∨ rows = [((), after)]) ∧ PendingAt after.core target ∧
      (∀ (slot : Nat), before.core.values[slot]? = some .eliminated →
        after.core.values[slot]? = some .eliminated) ∧
      (rows = [((), after)] → ∀ source ∈ sources, source ≠ target →
        after.core.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), slot ∉ sources → slot ≠ target →
        after.core.values[slot]? = before.core.values[slot]?) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        after.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) := by
  induction sources generalizing inventory beforeCaller before memos with
  | nil =>
    refine ⟨0, 0, 0, [((), before)], beforeCaller, memos.query, memos, inventory, before,
      ?_, Post.refl initial, rfl, rfl, rfl, paths, storage, realized, counts, rfl,
      flags, .inr rfl, targetPending, ?_, ?_, ?_, ?_⟩
    · intro extra P H _largeP _largeH
      rfl
    · intro slot oldEliminated
      exact oldEliminated
    · intro _completed source member _different
      cases member
    · intro _slot _outside _different
      rfl
    · intro _slot _fragment stored
      exact stored
  | cons source rest ih =>
    have slots : source = target ∨ before.core.values[source]? = some .eliminated ∨
        ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
          before.core.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
          before.core.values[target]? = some (.unenumerated targetNode targetScs) := by
      obtain ⟨targetNode, targetScs, targetStored⟩ := targetPending
      rcases selected source (by simp) with ⟨sourceNode, sourceScs, sourceStored⟩ | eliminated
      · exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourceStored, targetStored⟩)
      · exact .inr (.inl eliminated)
    obtain ⟨headFuel, headP, headH, action, headCaller, headQueries, headMemos, headInventory,
      headRows, headAfter, headRun, headPost, headQuerySame, rawCached, headCounter,
      headRepresentatives, headPaths, headStorage, headRealized, headCounts, headWaiting,
      headFlags, noOpResult, liveResult⟩ :=
        cachedDispatch_complete formulas solver inventory beforeCaller before
          checkEmpty source target memos roots initial storage realized paths counts flags slots ranges.1
    have headFacts :
        SourcePruningEnumerationCachedAdapter.adapt headCaller.checked.native.machine.heap before source target
          (headRows.map (fun row => .ok (row.1, row.2.core))) = some headAfter ∧
        (headRows = [] ∨ headRows = [((), headAfter)]) ∧ PendingAt headAfter.core target ∧
        (∀ remaining ∈ rest, PendingOrEliminated headAfter.core remaining) ∧
        (∀ (slot : Nat), before.core.values[slot]? = some .eliminated →
          headAfter.core.values[slot]? = some .eliminated) ∧
        (source ≠ target → headRows = [((), headAfter)] →
          headAfter.core.values[source]? = some .eliminated) ∧
        (headRows = [] → headAfter = before) ∧
        (∀ (slot : Nat), slot ≠ source → slot ≠ target →
          headAfter.core.values[slot]? = before.core.values[slot]?) := by
      by_cases sameId : source = target
      · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inl sameId)
        rw [rowsSame, afterSame]
        refine ⟨?_, .inr rfl, targetPending, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.map_nil, SourcePruningEnumerationCachedAdapter.adapt,
            ite_eq_left sameId]
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro slot oldEliminated
          exact oldEliminated
        · intro different _completed
          exact False.elim (different sameId)
        · intro rejectedRows
          cases rejectedRows
        · intro _slot _sourceDifferent _targetDifferent
          rfl
      · by_cases sourceEliminated : before.core.values[source]? = some .eliminated
        · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inr sourceEliminated)
          rw [rowsSame, afterSame]
          refine ⟨?_, .inr rfl, targetPending, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [List.map_cons, List.map_nil, SourcePruningEnumerationCachedAdapter.adapt,
              ite_eq_right sameId, sourceEliminated]
          · intro remaining member
            exact selected remaining (by simp [member])
          · intro slot oldEliminated
            exact oldEliminated
          · intro _different _completed
            exact sourceEliminated
          · intro rejectedRows
            cases rejectedRows
          · intro _slot _sourceDifferent _targetDifferent
            rfl
        · obtain ⟨_sourceNode, _targetNode, merged, sourceScs, targetScs, sourceStored,
            targetStored, _computed, selectedResult⟩ :=
              liveResult sameId sourceEliminated
          by_cases rejected : merged = some 0
          · rw [ite_eq_left rejected] at selectedResult
            obtain ⟨rowsSame, afterSame⟩ := selectedResult
            rw [rowsSame, afterSame]
            refine ⟨rfl, .inl rfl, targetPending, ?_, ?_, ?_, ?_, ?_⟩
            · intro remaining member
              exact selected remaining (by simp [member])
            · intro slot oldEliminated
              exact oldEliminated
            · intro _different _completed
              cases _completed
            · intro _rejectedRows
              rfl
            · intro _slot _sourceDifferent _targetDifferent
              rfl
          · rw [ite_eq_right rejected] at selectedResult
            obtain ⟨rowsSame, coreSame, sourceAfter, targetAfter, sourceFlag, otherFlags⟩ := selectedResult
            have sourceInside : source < before.core.values.length := by
              exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound _elementEquality => bound)
            have targetInside : target < before.core.values.length := by
              exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound _elementEquality => bound)
            have classified : SourcePruningEnumerationNativeIndex.candidate
                headCaller.checked.native.machine.heap (.unenumerated merged (sourceScs ++ targetScs)) =
                  some (headAfter.expandable target) := by
              simpa only [targetAfter, Option.getD_some] using headFlags target
            have flagsSame :
                (fun (slot : Nat) => if slot = source then false else
                  if slot = target then headAfter.expandable target else before.expandable slot) =
                    headAfter.expandable := by
              funext slot
              by_cases sourceId : slot = source
              · subst slot
                simpa only [↓reduceIte] using sourceFlag.symm
              · by_cases targetId : slot = target
                · subst slot
                  simp only [ite_eq_right sourceId, ↓reduceIte]
                · simp only [ite_eq_right sourceId, ite_eq_right targetId]
                  exact (otherFlags slot sourceId targetId).symm
            have cacheSame :
                (⟨headAfter.core, (fun (slot : Nat) => if slot = source then false else
                  if slot = target then headAfter.expandable target else before.expandable slot),
                    before.waiting⟩ : EnumerationExpandableIndex.Cached Symbol Constraint) = headAfter := by
              rw [flagsSame, ←headWaiting]
            obtain ⟨pendingTarget, keptSlots⟩ := EnumerationCompleteness.assimilated_pending
              before.core target source merged (sourceScs ++ targetScs) (Ne.symm sameId)
                targetInside sourceInside
            refine ⟨?_, .inr rowsSame, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [rowsSame]
              simp only [List.map_cons, List.map_nil, SourcePruningEnumerationCachedAdapter.adapt,
                ite_eq_right sameId, sourceStored, targetAfter, Option.bind_some, classified, Option.map_some]
              exact congrArg some cacheSame
            · rw [coreSame]
              exact pendingTarget
            · intro remaining member
              rw [coreSame]
              exact keptSlots remaining (selected remaining (by simp [member]))
            · intro slot oldEliminated
              by_cases atTarget : slot = target
              · subst slot
                rw [targetStored] at oldEliminated
                cases oldEliminated
              by_cases atSource : slot = source
              · subst slot
                exact sourceAfter
              rw [coreSame, assimilation_frame before.core target source slot
                (.unenumerated merged (sourceScs ++ targetScs)) atTarget atSource]
              exact oldEliminated
            · intro _different _completed
              exact sourceAfter
            · intro rejectedRows
              rw [rowsSame] at rejectedRows
              cases rejectedRows
            · intro slot sourceDifferent targetDifferent
              rw [coreSame]
              exact assimilation_frame before.core target source slot
                (.unenumerated merged (sourceScs ++ targetScs)) targetDifferent sourceDifferent
    rcases headFacts with ⟨headAdapted, headShape, headTarget, headSelected, headEliminated,
      headSource, headRejectedSame, headFrame⟩
    have headOrigin : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        headAfter.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment) := by
      intro slot fragment stored
      rcases headShape with rejected | completed
      · simpa only [headRejectedSame rejected] using stored
      · by_cases atTarget : slot = target
        · subst slot
          obtain ⟨node, scs, pendingStored⟩ := headTarget
          rw [pendingStored] at stored
          cases stored
        · by_cases atSource : slot = source
          · subst slot
            rw [headSource atTarget completed] at stored
            cases stored
          · simpa only [headFrame slot atSource atTarget] using stored
    rcases headShape with headRejected | headCompleted
    · obtain rfl := (headRejectedSame headRejected).symm
      refine ⟨headFuel, headP, headH, [], headCaller, headQueries, headMemos, headInventory,
        before, ?_, headPost, headQuerySame, headCounter, headRepresentatives, headPaths,
        headStorage, headRealized, headCounts, headWaiting, headFlags, .inl rfl,
        headTarget, headEliminated, ?_, ?_, ?_⟩
      · intro extra P H largeP largeH
        simp only [fold, cachedAdapter,
          headRun extra P H largeP largeH, rawCached, headRejected, List.map_nil,
          SourcePruningEnumerationCachedAdapter.adapt]
      · intro completed
        cases completed
      · intro _slot _outside _different
        rfl
      · intro _slot _fragment stored
        exact stored
    ·
      have tailRanges : Ranges checkEmpty rest
          headCaller headAfter.core target headMemos.query := by
        simpa only [headQuerySame, Nat.add_zero] using
          ranges.2 headFuel headP headH action headCaller headQueries headAfter.core
            (headRun 0 headP headH (Nat.le_refl _) (Nat.le_refl _))
            (by rw [rawCached, headCompleted]; rfl)
      obtain ⟨tailFuel, tailP, tailH, tailRows, tailCaller, tailQueries, tailMemos, tailInventory,
        tailAfter, tailRun, tailPost, tailQuerySame, tailCounter, tailRepresentatives, tailPaths,
        tailStorage, tailRealized, tailCounts, tailWaiting, tailFlags, tailShape, tailTarget,
        tailEliminated, tailCompleted, tailFrame, tailOrigin⟩ :=
          ih headInventory headCaller headAfter headMemos headPost.context headStorage headRealized
            headPaths headCounts headFlags headTarget headSelected tailRanges
      have headAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
          cachedAdapter checkEmpty (headFuel + tailFuel + extra) P H
            beforeCaller before source target memos.query =
            (.ok (some (headRows.map (fun row => .ok (row.1, row.2.core)))),
              headCaller, headQueries, some headAfter) := by
        intro extra P H largeP largeH
        rw [Nat.add_assoc]
        simp only [cachedAdapter,
          headRun (tailFuel + extra) P H
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH),
          rawCached, headAdapted]
      have tailAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
          fold checkEmpty (headFuel + tailFuel + extra) P H rest
            headCaller headAfter target headMemos.query =
            ((.ok (some (tailRows.map (fun row => .ok (row.1, row.2.core)))),
              tailCaller, tailQueries, tailAfter.core), some tailAfter) := by
        intro extra P H largeP largeH
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          tailRun (headFuel + extra) P H
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
      refine ⟨headFuel + tailFuel, max headP tailP, max headH tailH, tailRows, tailCaller,
        tailQueries, tailMemos, tailInventory, tailAfter, ?_, headPost.trans tailPost,
        tailQuerySame, tailCounter.trans headCounter, tailRepresentatives.trans headRepresentatives,
        tailPaths, tailStorage, tailRealized, tailCounts, tailWaiting.trans headWaiting,
        tailFlags, tailShape, tailTarget, ?_, ?_, ?_, ?_⟩
      · intro extra P H largeP largeH
        rw [fold, headAt extra P H largeP largeH]
        simp only [headCompleted, List.map_cons, List.map_nil]
        change fold checkEmpty (headFuel + tailFuel + extra) P H rest
          headCaller headAfter target headQueries = _
        rw [←headQuerySame]
        exact tailAt extra P H largeP largeH
      · intro slot oldEliminated
        exact tailEliminated slot (headEliminated slot oldEliminated)
      · intro completed remaining member different
        rcases List.mem_cons.mp member with memberHead | memberRest
        · subst remaining
          exact tailEliminated source (headSource different headCompleted)
        · exact tailCompleted completed remaining memberRest different
      · intro slot outside different
        have headDifferent : slot ≠ source := by
          intro same
          exact outside (List.mem_cons.mpr (.inl same))
        have tailOutside : slot ∉ rest := fun member => outside (List.mem_cons_of_mem source member)
        exact (tailFrame slot tailOutside different).trans (headFrame slot headDifferent different)
      · intro slot fragment stored
        exact headOrigin slot fragment (tailOrigin slot fragment stored)

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
