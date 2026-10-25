import MicroCFTA.SourcePruningEnumerationCachedFold

namespace MicroCFTA.SourcePruningEnumerationCachedFoldCompletion
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Derive common finite bounds and a valid cache for the admitted ordered fold. -/
theorem complete
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
    (ranges : SourcePruningEnumerationFold.Ranges checkEmpty sources
      beforeCaller before.core target memos.query) :
    ∃ (fuel p h : Nat)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationCachedFold.run checkEmpty (fuel + extra) P H sources
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
        after.core.values[source]? = some .eliminated) := by
  induction sources generalizing inventory beforeCaller before memos with
  | nil =>
    refine ⟨0, 0, 0, [((), before)], beforeCaller, memos.query, memos, inventory, before,
      ?_, Post.refl initial, rfl, rfl, rfl, paths, storage, realized, counts, rfl,
      flags, .inr rfl, targetPending, ?_, ?_⟩
    · intro extra P H _largeP _largeH
      rfl
    · intro slot oldEliminated
      exact oldEliminated
    · intro _completed source member _different
      cases member
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
        SourcePruningEnumerationCachedDispatch.complete formulas solver inventory beforeCaller before
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
        (headRows = [] → headAfter = before) := by
      by_cases sameId : source = target
      · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inl sameId)
        rw [rowsSame, afterSame]
        refine ⟨?_, .inr rfl, targetPending, ?_, ?_, ?_, ?_⟩
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
      · by_cases sourceEliminated : before.core.values[source]? = some .eliminated
        · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inr sourceEliminated)
          rw [rowsSame, afterSame]
          refine ⟨?_, .inr rfl, targetPending, ?_, ?_, ?_, ?_⟩
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
        · obtain ⟨_sourceNode, _targetNode, merged, sourceScs, targetScs, sourceStored,
            targetStored, _computed, selectedResult, _optionalOrigin, _queriedOrigin⟩ :=
              liveResult sameId sourceEliminated
          by_cases rejected : merged = some 0
          · rw [ite_eq_left rejected] at selectedResult
            obtain ⟨rowsSame, afterSame⟩ := selectedResult
            rw [rowsSame, afterSame]
            refine ⟨rfl, .inl rfl, targetPending, ?_, ?_, ?_, ?_⟩
            · intro remaining member
              exact selected remaining (by simp [member])
            · intro slot oldEliminated
              exact oldEliminated
            · intro _different _completed
              cases _completed
            · intro _rejectedRows
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
            refine ⟨?_, .inr rowsSame, ?_, ?_, ?_, ?_, ?_⟩
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
    rcases headFacts with ⟨headAdapted, headShape, headTarget, headSelected, headEliminated,
      headSource, headRejectedSame⟩
    rcases headShape with headRejected | headCompleted
    · obtain rfl := (headRejectedSame headRejected).symm
      refine ⟨headFuel, headP, headH, [], headCaller, headQueries, headMemos, headInventory,
        before, ?_, headPost, headQuerySame, headCounter, headRepresentatives, headPaths,
        headStorage, headRealized, headCounts, headWaiting, headFlags, .inl rfl,
        headTarget, headEliminated, ?_⟩
      · intro extra P H largeP largeH
        simp only [SourcePruningEnumerationCachedFold.run, SourcePruningEnumerationCachedAdapter.run,
          headRun extra P H largeP largeH, rawCached, headRejected, List.map_nil,
          SourcePruningEnumerationCachedAdapter.adapt]
      · intro completed
        cases completed
    ·
      have tailRanges : SourcePruningEnumerationFold.Ranges checkEmpty rest
          headCaller headAfter.core target headMemos.query := by
        simpa only [headQuerySame, Nat.add_zero] using
          ranges.2 headFuel headP headH action headCaller headQueries headAfter.core
            (headRun 0 headP headH (Nat.le_refl _) (Nat.le_refl _))
            (by rw [rawCached, headCompleted]; rfl)
      obtain ⟨tailFuel, tailP, tailH, tailRows, tailCaller, tailQueries, tailMemos, tailInventory,
        tailAfter, tailRun, tailPost, tailQuerySame, tailCounter, tailRepresentatives, tailPaths,
        tailStorage, tailRealized, tailCounts, tailWaiting, tailFlags, tailShape, tailTarget,
        tailEliminated, tailCompleted⟩ :=
          ih headInventory headCaller headAfter headMemos headPost.context headStorage headRealized
            headPaths headCounts headFlags headTarget headSelected tailRanges
      have headAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
          SourcePruningEnumerationCachedAdapter.run checkEmpty (headFuel + tailFuel + extra) P H
            beforeCaller before source target memos.query =
            (.ok (some (headRows.map (fun row => .ok (row.1, row.2.core)))),
              headCaller, headQueries, some headAfter) := by
        intro extra P H largeP largeH
        rw [Nat.add_assoc]
        simp only [SourcePruningEnumerationCachedAdapter.run,
          headRun (tailFuel + extra) P H
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH),
          rawCached, headAdapted]
      have tailAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
          SourcePruningEnumerationCachedFold.run checkEmpty (headFuel + tailFuel + extra) P H rest
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
        tailFlags, tailShape, tailTarget, ?_, ?_⟩
      · intro extra P H largeP largeH
        rw [SourcePruningEnumerationCachedFold.run, headAt extra P H largeP largeH]
        simp only [headCompleted, List.map_cons, List.map_nil]
        change SourcePruningEnumerationCachedFold.run checkEmpty (headFuel + tailFuel + extra) P H rest
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

end MicroCFTA.SourcePruningEnumerationCachedFoldCompletion
