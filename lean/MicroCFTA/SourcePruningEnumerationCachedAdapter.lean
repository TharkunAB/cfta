import MicroCFTA.SourcePruningEnumerationCachedDispatch

namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Reconstruct the cache from an actual raw row with explicit partiality. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (source target : Nat)
    (raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))) :
    Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match raw with
  | [] => some before
  | [.ok ((), core)] =>
      if source = target then some before else
        match before.core.values[source]? with
        | some .eliminated => some before
        | _ =>
            (core.values[target]?).bind fun value =>
              (SourcePruningEnumerationNativeIndex.candidate heap value).map fun flag =>
                ⟨core, (fun slot => if slot = source then false else
                  if slot = target then flag else before.expandable slot), before.waiting⟩
  | _ => none

/-- Run dispatch and its captured action once, with a separate cache receipt. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (source target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before.core source target queries with
  | (.error fault, reachedCaller, savedQueries) =>
      (.error fault, reachedCaller, savedQueries, none)
  | (.ok none, reachedCaller, savedQueries) =>
      (.ok none, reachedCaller, savedQueries, none)
  | (.ok (some action), reachedCaller, savedQueries) =>
      let raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)) :=
        ExceptT.run (action before.core)
      (.ok (some raw), reachedCaller, savedQueries,
        adapt reachedCaller.checked.native.machine.heap before source target raw)

/-- Derive finite cached execution from the actual dispatcher completion. -/
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
    ∃ (fuel p h : Nat)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra P H, p ≤ P → h ≤ H →
        run checkEmpty (fuel + extra) P H beforeCaller before source target memos.query =
          (.ok (some (rows.map (fun row => .ok (row.1, row.2.core)))),
            afterCaller, savedQueries, some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (rows = [] ∨ rows = [((), after)]) ∧
      ((source = target ∨ before.core.values[source]? = some .eliminated) →
        rows = [((), before)] ∧ after = before ∧
        afterCaller = beforeCaller ∧ final = memos ∧ next = inventory) := by
  obtain ⟨fuel, p, h, action, afterCaller, savedQueries, final, next, rows, after,
    actual, post, savedSame, rawCached, counterSame, forestSame, afterPaths, afterStorage,
    cacheRealized, afterCounts, waitingSame, afterFlags, noOpResult, liveResult⟩ :=
      SourcePruningEnumerationCachedDispatch.complete formulas solver inventory beforeCaller
        before checkEmpty source target memos roots initial storage realized paths counts flags slots ranges
  have adapted :
      adapt afterCaller.checked.native.machine.heap before source target
        (rows.map (fun row => .ok (row.1, row.2.core))) = some after ∧
      (rows = [] ∨ rows = [((), after)]) := by
    by_cases sameId : source = target
    · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inl sameId)
      rw [rowsSame, afterSame]
      refine ⟨?_, Or.inr rfl⟩
      simp only [List.map_cons, List.map_nil, adapt, ite_eq_left sameId]
    · by_cases sourceEliminated : before.core.values[source]? = some .eliminated
      · obtain ⟨rowsSame, afterSame, _callerSame, _finalSame, _nextSame⟩ := noOpResult (Or.inr sourceEliminated)
        rw [rowsSame, afterSame]
        refine ⟨?_, Or.inr rfl⟩
        simp only [List.map_cons, List.map_nil, adapt, ite_eq_right sameId, sourceEliminated]
      · obtain ⟨_sourceNode, _targetNode, merged, sourceScs, targetScs, sourceStored,
          _targetStored, _computed, selectedResult, _optionalOrigin, _queriedOrigin⟩ :=
            liveResult sameId sourceEliminated
        by_cases rejected : merged = some 0
        · rw [ite_eq_left rejected] at selectedResult
          obtain ⟨rowsSame, afterSame⟩ := selectedResult
          rw [rowsSame, afterSame]
          exact ⟨rfl, Or.inl rfl⟩
        · rw [ite_eq_right rejected] at selectedResult
          obtain ⟨rowsSame, _coreSame, _sourceAfter, targetAfter, sourceFlag, otherFlags⟩ := selectedResult
          have classified : SourcePruningEnumerationNativeIndex.candidate
              afterCaller.checked.native.machine.heap (.unenumerated merged (sourceScs ++ targetScs)) =
                some (after.expandable target) := by
            simpa only [targetAfter, Option.getD_some] using afterFlags target
          have flagsSame :
              (fun (slot : Nat) => if slot = source then false else
                if slot = target then after.expandable target else before.expandable slot) =
                  after.expandable := by
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
              (⟨after.core, (fun (slot : Nat) => if slot = source then false else
                if slot = target then after.expandable target else before.expandable slot),
                  before.waiting⟩ : EnumerationExpandableIndex.Cached Symbol Constraint) = after := by
            rw [flagsSame, ←waitingSame]
          refine ⟨?_, Or.inr rowsSame⟩
          rw [rowsSame]
          simp only [List.map_cons, List.map_nil, adapt, ite_eq_right sameId, sourceStored,
            targetAfter, Option.bind_some, classified, Option.map_some]
          exact congrArg some cacheSame
  refine ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    ?_, post, savedSame, counterSame, forestSame, afterPaths, afterStorage,
    cacheRealized, afterCounts, waitingSame, afterFlags, adapted.2, noOpResult⟩
  intro extra P H pBound hBound
  simp only [run, actual extra P H pBound hBound, rawCached, adapted.1]

end MicroCFTA.SourcePruningEnumerationCachedAdapter
