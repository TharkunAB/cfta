import MicroCFTA.SourcePruningEnumerationCachedAssimilation

namespace MicroCFTA.SourcePruningEnumerationCachedDispatch
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Derive cached rows from one actual dispatcher completion and its returned heap. -/
theorem complete
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
        SourcePruningEnumerationDispatch.dispatch checkEmpty (fuel + extra) P H
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
            (∀ (slot : Nat), slot ≠ source → slot ≠ target → after.expandable slot = before.expandable slot)) ∧
          ((sourceNode = none ∨ targetNode = none) →
            merged = sourceNode.orElse (fun _ => targetNode) ∧
            afterCaller = beforeCaller ∧ final = memos ∧ next = inventory) ∧
          (∀ leftHandle rightHandle, sourceNode = some leftHandle → targetNode = some rightHandle →
            ∃ (left right query replacement : Node) (queried : Checked width) (handle : Nat),
              lookupNode beforeCaller.checked.native.machine.heap leftHandle = some left ∧
              lookupNode beforeCaller.checked.native.machine.heap rightHandle = some right ∧
              next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
                beforeCaller.checked query queried memos ∧
              merged = some handle ∧ encodeNode replacement = some handle ∧
              lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
              Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) ∧
              (checkEmpty = false → replacement = query ∧
                afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller queried
                  beforeCaller.fourth beforeCaller.merge ∧ final = memos) ∧
              (checkEmpty = true → ∃ reached answer guardSaved,
                SourceEndpointMemo.run query memos.query = (reached, guardSaved) ∧
                SourceEndpointMemoCorrect.Checked queried.native.machine.heap memos.query
                  (SourceCurrentEmptinessMerge.reaches query) (reached, guardSaved) ∧
                (∀ P H, p ≤ P → h ≤ H →
                  SourcePruningEnumerationEnabledEmpty.check P H query queried beforeCaller.fourth memos.query =
                    (.done answer afterCaller.checked afterCaller.fourth, guardSaved)) ∧
                savedQueries = guardSaved ∧ replacement = (if answer then .empty else query) ∧
                (reached = false → answer = false ∧ afterCaller.checked = queried ∧
                  afterCaller.fourth = beforeCaller.fourth ∧ final = {memos with query := guardSaved}) ∧
                (reached = true →
                  ∃ (reachedPhysical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula),
                    afterCaller.checked = SourceCurrentAllocatedQueryMemo.advancePhysical queried reachedPhysical ∧
                    ∃ actual : SourceCurrentConjunctionMemo.Call 1000 beforeCaller.fourth query
                        (physical queried) answer reachedPhysical afterCaller.fourth,
                      SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final)))) := by
  obtain ⟨fuel, p, h, action, afterCaller, savedQueries, final, next,
    actual, post, savedSame, heapRealized, noOpResult, liveResult⟩ :=
      SourcePruningEnumerationDispatch.dispatch_complete formulas solver inventory beforeCaller
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
        computed, result, optionalOrigin, queriedOrigin⟩

end MicroCFTA.SourcePruningEnumerationCachedDispatch
