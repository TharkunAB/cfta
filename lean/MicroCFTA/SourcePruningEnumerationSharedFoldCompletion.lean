import MicroCFTA.SourcePruningEnumerationSharedFoldResources

/-!
# Complete shared folds from current ordered reservations

The internal range condition is derived from the current entry and each
actual successful singleton. The public resource producer supplies it from
one shared reservation. It constructs stable finite completion, the actual
stopped prefix, full Post and the same returned caller resources.
No external future-range callback or completed whole driver is required.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed step advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Each successful shared prefix supplies the native ranges of its next literal query. -/
def Ranges
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries) : Prop :=
  match sources with
  | [] => True
  | source :: rest =>
      (if source = target then True else
        match before.values[source]?, before.values[target]? with
        | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
            match lookupNode beforeCaller.checked.native.machine.heap left,
                lookupNode beforeCaller.checked.native.machine.heap right with
            | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
                beforeCaller.checked
            | _, _ => True
        | _, _ => True) ∧
      ∀ nativeFuel p h action afterCaller saved after,
        SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
          beforeCaller before source target queries = (.ok (some action), afterCaller, saved) →
        ExceptT.run (action before) = [.ok ((), after)] →
        Ranges checkEmpty rest afterCaller after target saved

/-- Safe pending slots derive either the complete fold or its first rejection. -/
theorem rawFold_complete
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
      before.values[target]? = some (.unenumerated node scs))
    (selected : ∀ source ∈ sources, before.values[source]? = some .eliminated ∨
      ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
        before.values[source]? = some (.unenumerated node scs))
    (ranges : Ranges checkEmpty sources beforeCaller before target memos.query) :
    ∃ (fuel p h : Nat)
      (raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))
      (afterCaller : Caller width) (after : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra P H, p ≤ P → h ≤ H →
        rawFold checkEmpty (fuel + extra) P H sources beforeCaller before target memos.query =
          (.ok (some raw), afterCaller, savedQueries, after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      PendingRealized afterCaller.checked.native.machine.heap after ∧
      (raw = [] ∨ raw = [.ok ((), after)]) ∧
      (raw = [.ok ((), after)] →
        (∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
          after.values[target]? = some (.unenumerated node scs)) ∧
        ∀ source ∈ sources, source ≠ target → after.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), before.values[slot]? = some .eliminated → after.values[slot]? = some .eliminated) ∧
      after.values.length = before.values.length ∧
      after.representatives = before.representatives ∧ after.counter = before.counter ∧
      after.obligations = before.obligations ∧ after.expansionAncestry = before.expansionAncestry ∧
      (∀ slot, slot ≠ target → after.recursionAncestry slot = before.recursionAncestry slot) ∧
      (raw = [] →
        ∃ («prefix» : List Nat) (source : Nat) (suffix : List Nat)
          (prefixCaller : Caller width) (prefixEnum : EnumerationState.State Symbol Constraint)
          (prefixQueries : Queries) (action : EnumerateM Symbol Constraint Unit),
          sources = «prefix» ++ source :: suffix ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            rawFold checkEmpty (fuel + extra) P H «prefix» beforeCaller before target memos.query =
              (.ok (some [.ok ((), prefixEnum)]), prefixCaller, prefixQueries, prefixEnum)) ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationSharedDispatch.dispatch checkEmpty (fuel + extra) P H
              prefixCaller prefixEnum source target prefixQueries =
                (.ok (some action), afterCaller, savedQueries)) ∧
          ExceptT.run (action prefixEnum) = [] ∧ after = prefixEnum) := by
  induction sources generalizing inventory beforeCaller before memos with
  | nil =>
    refine ⟨0, 0, 0, [.ok ((), before)], beforeCaller, before, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, .inr rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro extra P H _largeP _largeH
      rfl
    · intro _completed
      exact ⟨targetPending, by simp⟩
    · intro slot oldEliminated
      exact oldEliminated
    · intro slot _different
      rfl
    · intro rejected
      cases rejected
  | cons source rest ih =>
    have headRanges : if source = target then True else
      match before.values[source]?, before.values[target]? with
      | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap left,
              lookupNode beforeCaller.checked.native.machine.heap right with
          | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
              beforeCaller.checked
          | _, _ => True
      | _, _ => True := by
      exact ranges.1
    have headPacket :
      ∃ (headFuel headP headH : Nat) (action : EnumerateM Symbol Constraint Unit)
        (headCaller : Caller width) (headAfter : EnumerationState.State Symbol Constraint)
        (headQueries : Queries) (headMemos : Memos) (headInventory : Inventory),
        (∀ extra P H, headP ≤ P → headH ≤ H →
          SourcePruningEnumerationSharedDispatch.dispatch checkEmpty (headFuel + extra) P H
            beforeCaller before source target memos.query = (.ok (some action), headCaller, headQueries)) ∧
        Post formulas solver headInventory beforeCaller headCaller headMemos ∧ headMemos.query = headQueries ∧
        PendingRealized headCaller.checked.native.machine.heap headAfter ∧
        (ExceptT.run (action before) = [] ∨ ExceptT.run (action before) = [.ok ((), headAfter)]) ∧
        (ExceptT.run (action before) = [] → headAfter = before) ∧
        (∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
          headAfter.values[target]? = some (.unenumerated node scs)) ∧
        (∀ remaining ∈ rest, headAfter.values[remaining]? = some .eliminated ∨
          ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
            headAfter.values[remaining]? = some (.unenumerated node scs)) ∧
        (source ≠ target → ExceptT.run (action before) = [.ok ((), headAfter)] →
          headAfter.values[source]? = some .eliminated) ∧
        (∀ (slot : Nat), before.values[slot]? = some .eliminated → headAfter.values[slot]? = some .eliminated) ∧
        headAfter.values.length = before.values.length ∧
        headAfter.representatives = before.representatives ∧ headAfter.counter = before.counter ∧
        headAfter.obligations = before.obligations ∧ headAfter.expansionAncestry = before.expansionAncestry ∧
        (∀ slot, slot ≠ target → headAfter.recursionAncestry slot = before.recursionAncestry slot) := by
      obtain ⟨targetNode, targetScs, targetPendingStored⟩ := targetPending
      have sourceSelected : before.values[source]? = some .eliminated ∨
        ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
          before.values[source]? = some (.unenumerated node scs) := by
        exact selected source (by simp)
      have slots : source = target ∨ before.values[source]? = some .eliminated ∨
        ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
          before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
          before.values[target]? = some (.unenumerated targetNode targetScs) := by
        rcases sourceSelected with storedEliminated | ⟨sourceNode, sourceScs, sourcePendingStored⟩
        · exact .inr (.inl storedEliminated)
        · exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourcePendingStored, targetPendingStored⟩)
      obtain ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, dispatchQueries, dispatchMemos,
        dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame, unchangedRealized,
        noopOutcome, changedOutcome⟩ := SourcePruningEnumerationSharedDispatch.dispatch_complete
          formulas solver inventory beforeCaller before checkEmpty source target memos initial realized slots headRanges
      by_cases same : source = target
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inr (noopOutcome (.inl same)).1, ?_, ⟨targetNode, targetScs, targetPendingStored⟩,
          ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro different _completed
          exact False.elim (different same)
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      by_cases eliminated : before.values[source]? = some .eliminated
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inr (noopOutcome (.inr eliminated)).1, ?_, ⟨targetNode, targetScs, targetPendingStored⟩,
          ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro _different _completed
          exact eliminated
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
        actionRaw, surviving, _optionalOutcome, _presentOutcome⟩ := changedOutcome same eliminated
      by_cases empty : merged = some 0
      · refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller, before, dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          unchangedRealized, .inl (by simpa only [ite_eq_left empty] using actionRaw), ?_,
          ⟨targetNode, targetScs, targetStored⟩, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _rejected
          rfl
        · intro remaining member
          exact selected remaining (by simp [member])
        · intro _different completed
          rw [actionRaw, ite_eq_left empty] at completed
          cases completed
        · intro slot oldEliminated
          exact oldEliminated
        · intro slot _different
          rfl
      · obtain ⟨targetAfterStored, sourceAfterStored, changedRealized⟩ := surviving empty
        have changedFrame :
          (∀ (slot : Nat), before.values[slot]? = some .eliminated →
            (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[slot]? = some .eliminated) ∧
          (∀ remaining ∈ rest,
            (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[remaining]? = some .eliminated ∨
              ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
                (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[remaining]? =
                  some (.unenumerated node scs)) := by
          constructor
          · intro slot oldEliminated
            by_cases atTarget : slot = target
            · subst slot
              rw [targetStored] at oldEliminated
              cases oldEliminated
            by_cases atSource : slot = source
            · subst slot
              exact sourceAfterStored
            simpa only [assimilated, List.getElem?_set_ne (Ne.symm atSource),
              List.getElem?_set_ne (Ne.symm atTarget)] using oldEliminated
          · intro remaining member
            by_cases remainingTarget : remaining = target
            · subst remaining
              exact .inr ⟨merged, sourceScs ++ targetScs, targetAfterStored⟩
            by_cases remainingSource : remaining = source
            · subst remaining
              exact .inl sourceAfterStored
            rcases selected remaining (by simp [member]) with oldEliminated | ⟨oldNode, oldScs, oldPending⟩
            · exact .inl (by simpa only [assimilated, List.getElem?_set_ne (Ne.symm remainingSource),
                List.getElem?_set_ne (Ne.symm remainingTarget)] using oldEliminated)
            · exact .inr ⟨oldNode, oldScs, by
                simpa only [assimilated, List.getElem?_set_ne (Ne.symm remainingSource),
                  List.getElem?_set_ne (Ne.symm remainingTarget)] using oldPending⟩
        refine ⟨dispatchFuel, dispatchP, dispatchH, action, dispatchCaller,
          assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)), dispatchQueries,
          dispatchMemos, dispatchInventory, dispatchStable, dispatchPost, dispatchQuerySame,
          changedRealized, .inr (by simpa only [ite_eq_right empty] using actionRaw), ?_,
          ⟨merged, sourceScs ++ targetScs, targetAfterStored⟩, changedFrame.2, ?_, changedFrame.1,
          ?_, rfl, rfl, rfl, rfl, ?_⟩
        · intro rejected
          rw [actionRaw, ite_eq_right empty] at rejected
          cases rejected
        · intro _different _completed
          exact sourceAfterStored
        · simp only [assimilated, List.length_set]
        · intro slot different
          simp only [assimilated, ite_eq_right different]
    obtain ⟨headFuel, headP, headH, action, headCaller, headAfter, headQueries, headMemos, headInventory,
      headRun, headPost, headQuerySame, headRealized, headShape, headRejectedSame, headTarget, headSelected,
      headSource, headEliminated, headLength, headRepresentatives, headCounter, headObligations,
      headExpansion, headAncestry⟩ := headPacket
    rcases headShape with headRejected | headCompleted
    · obtain rfl := (headRejectedSame headRejected).symm
      refine ⟨headFuel, headP, headH, [], headCaller, before, headQueries, headMemos, headInventory,
        ?_, headPost, headQuerySame, headRealized, .inl rfl, ?_, headEliminated,
        headLength, headRepresentatives, headCounter, headObligations, headExpansion, headAncestry, ?_⟩
      · intro extra P H largeP largeH
        simp only [rawFold, headRun extra P H largeP largeH, headRejected]
      · intro completed
        cases completed
      · intro _rejected
        exact ⟨[], source, rest, beforeCaller, before, memos.query, action,
          rfl, by intros; rfl, headRun, headRejected, rfl⟩
    ·
      have tailRanges : Ranges checkEmpty rest headCaller headAfter target headMemos.query := by
        simpa only [headQuerySame, Nat.add_zero] using
          ranges.2 headFuel headP headH action headCaller headQueries headAfter
            (headRun 0 headP headH (Nat.le_refl _) (Nat.le_refl _)) headCompleted
      obtain ⟨tailFuel, tailP, tailH, tailRaw, tailCaller, tailAfter, tailQueries, tailMemos, tailInventory,
        tailRun, tailPost, tailQuerySame, tailRealized, tailShape, tailCompleted, tailEliminated,
        tailLength, tailRepresentatives, tailCounter, tailObligations, tailExpansion, tailAncestry,
        tailRejection⟩ := ih headInventory headCaller headAfter headMemos headPost.context
          headRealized headTarget headSelected tailRanges
      have headAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
        SourcePruningEnumerationSharedDispatch.dispatch checkEmpty (headFuel + tailFuel + extra) P H
          beforeCaller before source target memos.query = (.ok (some action), headCaller, headQueries) := by
        intro extra P H largeP largeH
        simpa only [Nat.add_assoc] using headRun (tailFuel + extra) P H
          (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
      have tailAt : ∀ extra P H, max headP tailP ≤ P → max headH tailH ≤ H →
        rawFold checkEmpty (headFuel + tailFuel + extra) P H rest headCaller headAfter target headMemos.query =
          (.ok (some tailRaw), tailCaller, tailQueries, tailAfter) := by
        intro extra P H largeP largeH
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tailRun (headFuel + extra) P H
          (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
      refine ⟨headFuel + tailFuel, max headP tailP, max headH tailH, tailRaw, tailCaller, tailAfter,
        tailQueries, tailMemos, tailInventory, ?_, headPost.trans tailPost, tailQuerySame,
        tailRealized, tailShape, ?_, ?_, tailLength.trans headLength, tailRepresentatives.trans headRepresentatives,
        tailCounter.trans headCounter, tailObligations.trans headObligations, tailExpansion.trans headExpansion,
        ?_, ?_⟩
      · intro extra P H largeP largeH
        rw [rawFold, headAt extra P H largeP largeH]
        dsimp only
        rw [headCompleted]
        rw [← headQuerySame]
        exact tailAt extra P H largeP largeH
      · intro completed
        refine ⟨(tailCompleted completed).1, ?_⟩
        intro remaining member different
        rcases List.mem_cons.mp member with memberHead | memberRest
        · subst remaining
          exact tailEliminated source (headSource different headCompleted)
        · exact (tailCompleted completed).2 remaining memberRest different
      · intro slot oldEliminated
        exact tailEliminated slot (headEliminated slot oldEliminated)
      · intro slot different
        exact (tailAncestry slot different).trans (headAncestry slot different)
      · intro rejected
        obtain ⟨«prefix», rejectSource, suffix, prefixCaller, prefixEnum, prefixQueries, rejectAction,
          split, prefixRun, rejectRun, rejectRaw, rejectedAfter⟩ := tailRejection rejected
        refine ⟨source :: «prefix», rejectSource, suffix, prefixCaller, prefixEnum, prefixQueries, rejectAction,
          ?_, ?_, ?_, rejectRaw, rejectedAfter⟩
        · simp only [List.cons_append, split]
        · intro extra P H largeP largeH
          rw [rawFold, headAt extra P H largeP largeH]
          dsimp only
          rw [headCompleted]
          rw [← headQuerySame]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixRun (headFuel + extra) P H
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
        · intro extra P H largeP largeH
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rejectRun (headFuel + extra) P H
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)


variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Current shared reservations derive all range obligations of the actual ordered fold. -/
theorem initial_ranges (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    Ranges checkEmpty sources beforeCaller before target memos.query := by
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil => trivial
  | cons source rest ih =>
      refine ⟨SourcePruningEnumerationSharedDispatch.initial_ranges seed.2 beforeCaller before source target
        initial.ready realized fits reserved.head, ?_⟩
      intro n p h action afterCaller saved after observed completed
      obtain ⟨next, final, post, querySame, afterRealized, afterTarget, afterSelected, afterFits, afterKnown⟩ :=
        observed_singleton seed formulas solver inventory beforeCaller before source target rest checkEmpty memos
          initial realized targetPending selected fits reserved.head known observed completed
      rw [← querySame]
      exact ih (step seed) next afterCaller after final post.context afterRealized afterTarget afterSelected
        afterFits reserved.tail afterKnown


/-- Current entries and one shared reservation construct the complete resource-bounded fold. -/
theorem rawFold_complete_resources
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
      before.values[target]? = some (.unenumerated node scs))
    (selected : ∀ source ∈ sources, before.values[source]? = some .eliminated ∨
      ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
        before.values[source]? = some (.unenumerated node scs))
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (fuel p h : Nat)
      (raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))
      (afterCaller : Caller (bits + 2)) (after : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra P H, p ≤ P → h ≤ H →
        rawFold checkEmpty (fuel + extra) P H sources beforeCaller before target memos.query =
          (.ok (some raw), afterCaller, savedQueries, after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      PendingRealized afterCaller.checked.native.machine.heap after ∧
      (raw = [] ∨ raw = [.ok ((), after)]) ∧
      (raw = [.ok ((), after)] →
        (∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
          after.values[target]? = some (.unenumerated node scs)) ∧
        ∀ source ∈ sources, source ≠ target → after.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), before.values[slot]? = some .eliminated → after.values[slot]? = some .eliminated) ∧
      after.values.length = before.values.length ∧
      after.representatives = before.representatives ∧ after.counter = before.counter ∧
      after.obligations = before.obligations ∧ after.expansionAncestry = before.expansionAncestry ∧
      (∀ slot, slot ≠ target → after.recursionAncestry slot = before.recursionAncestry slot) ∧
      (raw = [] →
        ∃ («prefix» : List Nat) (source : Nat) (suffix : List Nat)
          (prefixCaller : Caller (bits + 2)) (prefixEnum : EnumerationState.State Symbol Constraint)
          (prefixQueries : Queries) (action : EnumerateM Symbol Constraint Unit),
          sources = «prefix» ++ source :: suffix ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            rawFold checkEmpty (fuel + extra) P H «prefix» beforeCaller before target memos.query =
              (.ok (some [.ok ((), prefixEnum)]), prefixCaller, prefixQueries, prefixEnum)) ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationSharedDispatch.dispatch checkEmpty (fuel + extra) P H
              prefixCaller prefixEnum source target prefixQueries =
                (.ok (some action), afterCaller, savedQueries)) ∧
          ExceptT.run (action prefixEnum) = [] ∧ after = prefixEnum) ∧
      Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap := by
  have selectedPending : ∀ source ∈ sources, EnumerationCompleteness.PendingOrEliminated before source := by
    intro source member
    exact Or.symm (selected source member)
  have ranges := initial_ranges seed formulas solver inventory beforeCaller before sources
    checkEmpty target memos initial realized targetPending selectedPending fits reserved known
  obtain ⟨fuel, p, h, raw, afterCaller, after, saved, final, next,
      stable, post, querySame, afterRealized, shape, completed, eliminated, lengthSame,
      representatives, counter, obligations, expansion, ancestry, rejected⟩ :=
    rawFold_complete formulas solver inventory beforeCaller before sources checkEmpty target memos
      initial realized targetPending selected ranges
  have actual : rawFold checkEmpty fuel p h sources beforeCaller before target memos.query =
      (.ok (some raw), afterCaller, saved, after) := by
    simpa only [Nat.add_zero] using stable 0 p h (Nat.le_refl _) (Nat.le_refl _)
  have resources := rawFold_observed_resources seed formulas solver inventory beforeCaller before sources
    checkEmpty fuel p h target memos initial realized targetPending selectedPending fits reserved known actual
  exact ⟨fuel, p, h, raw, afterCaller, after, saved, final, next, stable, post, querySame,
    afterRealized, shape, completed, eliminated, lengthSame, representatives, counter, obligations,
    expansion, ancestry, rejected, resources.1, resources.2⟩

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
