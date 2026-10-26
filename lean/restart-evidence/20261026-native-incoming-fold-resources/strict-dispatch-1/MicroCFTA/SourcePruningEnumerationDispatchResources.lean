import MicroCFTA.SourcePruningEnumerationCachedDispatch
import MicroCFTA.SourcePruningEnumerationIncomingObservedResources

/-!
# Initial resources through the actual dispatcher

Current realized slots and numeric room admit the native query.
Every outer successful observation retains resources at its actual caller.
Missing actions and rejected raw rows remain distinct from outer errors.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "forecast" => SourcePruningEnumerationIncomingQuery.forecast
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
variable {EnumGuard : Type} {bits : Nat}
local notation "Core" => EnumerationState.State Symbol EnumGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

/-- Current pending slots derive the dispatcher admission from initial numeric room. -/
theorem initial_ranges (profile : Profile) (beforeCaller : Caller (bits + 2)) (before : Core)
    (source target : Nat) (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile) :
    if source = target then True else
      match before.values[source]?, before.values[target]? with
      | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap left,
              lookupNode beforeCaller.checked.native.machine.heap right with
          | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
              beforeCaller.checked
          | _, _ => True
      | _, _ => True := by
  by_cases same : source = target
  · simp only [ite_eq_left same]
  · simp only [ite_eq_right same]
    cases sourceStored : before.values[source]? with
    | none => trivial
    | some sourceValue =>
        cases sourceValue with
        | eliminated | enumerated => trivial
        | unenumerated sourceNode sourceScs =>
            cases sourceNode with
            | none => trivial
            | some leftHandle =>
                cases targetStored : before.values[target]? with
                | none => trivial
                | some targetValue =>
                    cases targetValue with
                    | eliminated | enumerated => trivial
                    | unenumerated targetNode targetScs =>
                        cases targetNode with
                        | none => trivial
                        | some rightHandle =>
                            cases leftLookup : lookupNode beforeCaller.checked.native.machine.heap leftHandle with
                            | none => trivial
                            | some left =>
                                cases rightLookup : lookupNode beforeCaller.checked.native.machine.heap rightHandle with
                                | none => trivial
                                | some right =>
                                    obtain ⟨first, firstLookup, leftAvailable, leftClosed⟩ :=
                                      realized source leftHandle sourceScs sourceStored
                                    obtain ⟨second, secondLookup, rightAvailable, rightClosed⟩ :=
                                      realized target rightHandle targetScs targetStored
                                    have firstSame := Option.some.inj (firstLookup.symm.trans leftLookup)
                                    have secondSame := Option.some.inj (secondLookup.symm.trans rightLookup)
                                    subst first
                                    subst second
                                    have actualRoom := fits.room room
                                    have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left
                                      beforeCaller.checked.native.machine.heap ready.good.native.machine.1.coherent
                                      leftAvailable leftClosed
                                    have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right
                                      beforeCaller.checked.native.machine.heap ready.good.native.machine.1.coherent
                                      rightAvailable rightClosed
                                    exact (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits
                                      beforeCaller.checked ready.good ready.semantic left right leftOriginal rightOriginal
                                      leftAvailable rightAvailable actualRoom.1 actualRoom.2.1 actualRoom.2.2).1

variable [DecidableEq Node]

/-- Every outer successful dispatcher observation retains its exact caller resources. -/
theorem observed_resources (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core)
    (checkEmpty : Bool) (nativeFuel p h source target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    {result : Option (EnumerateM Symbol EnumGuard Unit)}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries}
    (observed : dispatch checkEmpty nativeFuel p h beforeCaller before source target memos.query =
      (.ok result, afterCaller, savedQueries)) :
    Fits (forecast alphabet profile) afterCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) afterCaller.checked.native.machine.heap := by
  have unchanged : Fits (forecast alphabet profile) beforeCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) beforeCaller.checked.native.machine.heap := by
    refine ⟨fits.mono (SourcePruningEnumerationIncomingQuery.forecast_ge alphabet profile), ?_⟩
    intro key edge found
    exact SourceCurrentGeneratedQueryGuardResources.forecast_ge alphabet profile (known key edge found)
  simp only [dispatch, Id.run] at observed
  by_cases same : source = target
  · simp only [ite_eq_left same] at observed
    have callerSame := congrArg (fun output => output.2.1) observed
    dsimp only at callerSame
    rw [← callerSame]
    exact unchanged
  · simp only [ite_eq_right same] at observed
    cases sourceStored : before.values[source]? with
    | none =>
        simp only [sourceStored] at observed
        have callerSame := congrArg (fun output => output.2.1) observed
        dsimp only at callerSame
        rw [← callerSame]
        exact unchanged
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            simp only [sourceStored] at observed
            have callerSame := congrArg (fun output => output.2.1) observed
            dsimp only at callerSame
            rw [← callerSame]
            exact unchanged
        | enumerated _fragment =>
            cases targetStored : before.values[target]? <;>
              simp only [sourceStored, targetStored] at observed <;>
              have callerSame := congrArg (fun output => output.2.1) observed <;>
              dsimp only at callerSame <;>
              rw [← callerSame] <;> exact unchanged
        | unenumerated sourceNode sourceScs =>
            simp only [sourceStored] at observed
            cases targetStored : before.values[target]? with
            | none =>
                simp only [targetStored] at observed
                have callerSame := congrArg (fun output => output.2.1) observed
                dsimp only at callerSame
                rw [← callerSame]
                exact unchanged
            | some targetValue =>
                cases targetValue with
                | eliminated | enumerated =>
                    simp only [targetStored] at observed
                    have callerSame := congrArg (fun output => output.2.1) observed
                    dsimp only at callerSame
                    rw [← callerSame]
                    exact unchanged
                | unenumerated targetNode targetScs =>
                    simp only [targetStored] at observed
                    cases sourceNode with
                    | none =>
                        have callerSame := congrArg (fun output => output.2.1) observed
                        dsimp only at callerSame
                        rw [← callerSame]
                        exact unchanged
                    | some leftHandle =>
                        cases targetNode with
                        | none =>
                            have callerSame := congrArg (fun output => output.2.1) observed
                            dsimp only at callerSame
                            rw [← callerSame]
                            exact unchanged
                        | some rightHandle =>
                            cases leftLookup : lookupNode beforeCaller.checked.native.machine.heap leftHandle with
                            | none =>
                                simp only [leftLookup] at observed
                                have callerSame := congrArg (fun output => output.2.1) observed
                                dsimp only at callerSame
                                rw [← callerSame]
                                exact unchanged
                            | some left =>
                                simp only [leftLookup] at observed
                                cases rightLookup : lookupNode beforeCaller.checked.native.machine.heap rightHandle with
                                | none =>
                                    simp only [rightLookup] at observed
                                    have callerSame := congrArg (fun output => output.2.1) observed
                                    dsimp only at callerSame
                                    rw [← callerSame]
                                    exact unchanged
                                | some right =>
                                    obtain ⟨first, firstLookup, leftAvailable, leftClosed⟩ :=
                                      realized source leftHandle sourceScs sourceStored
                                    obtain ⟨second, secondLookup, rightAvailable, rightClosed⟩ :=
                                      realized target rightHandle targetScs targetStored
                                    have firstSame := Option.some.inj (firstLookup.symm.trans leftLookup)
                                    have secondSame := Option.some.inj (secondLookup.symm.trans rightLookup)
                                    subst first
                                    subst second
                                    simp only [rightLookup] at observed
                                    cases native : SourceEqualityNativeDemand.execute nativeFuel
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                    | yielded | failed | constraintError | blocked =>
                                        simp only [native] at observed
                                        cases observed
                                    | done query queried =>
                                        simp only [native, afterQuery] at observed
                                        cases phase : (if checkEmpty then
                                            SourcePruningEnumerationEnabledEmpty.check p h query queried
                                              beforeCaller.fourth memos.query
                                            else (.done false queried beforeCaller.fourth, memos.query)) with
                                        | mk outcome queries =>
                                            simp only [phase] at observed
                                            cases outcome with
                                            | failed =>
                                                simp only [Except.mapError] at observed
                                                cases observed
                                            | done answer checkedAfter saved =>
                                                have bounded := SourcePruningEnumerationIncomingQuery.raw_done_resources
                                                  alphabet profile formulas solver inventory beforeCaller left right
                                                  checkEmpty memos initial leftAvailable rightAvailable leftClosed
                                                  rightClosed fits room known native phase
                                                simp only [Except.mapError] at observed
                                                have callerSame := congrArg (fun output => output.2.1) observed
                                                dsimp only at callerSame
                                                rw [← callerSame]
                                                exact bounded

end MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationCachedDispatch
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "forecast" => SourcePruningEnumerationIncomingQuery.forecast
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
variable {bits : Nat}

/-- Initial resources retain every existing cached dispatcher receipt at the same caller. -/
theorem complete_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
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
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    ∃ (fuel p h : Nat) (action : EnumerateM Symbol Constraint Unit)
      (afterCaller : Caller (bits + 2)) (savedQueries : Queries) (final : Memos) (next : Inventory)
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
            ∃ (left right query replacement : Node) (queried : Checked (bits + 2)) (handle : Nat),
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
                      SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final)))) ∧
      Fits (forecast alphabet profile) afterCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) afterCaller.checked.native.machine.heap := by
  have ranges := SourcePruningEnumerationDispatch.initial_ranges profile beforeCaller before.core
    source target initial.ready realized fits room
  obtain ⟨fuel, p, h, action, afterCaller, savedQueries, final, next, rows, after,
    actual, post, savedSame, raw, counter, forest, afterPaths, afterStorage, afterRealized,
    afterCounts, waiting, afterFlags, noOp, live⟩ :=
    complete formulas solver inventory beforeCaller before checkEmpty source target memos roots
      initial storage realized paths counts flags slots ranges
  have observed := actual 0 p h (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  have resources := SourcePruningEnumerationDispatch.observed_resources alphabet profile formulas solver
    inventory beforeCaller before.core checkEmpty fuel p h source target memos
      initial realized fits room known observed
  exact ⟨fuel, p, h, action, afterCaller, savedQueries, final, next, rows, after,
    actual, post, savedSame, raw, counter, forest, afterPaths, afterStorage, afterRealized,
    afterCounts, waiting, afterFlags, noOp, live, resources.1, resources.2⟩

end MicroCFTA.SourcePruningEnumerationCachedDispatch
