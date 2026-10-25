import MicroCFTA.SourcePruningEnumerationEnabledEmpty
import MicroCFTA.SourcePruningEnumerationFinish
import MicroCFTA.SourceCurrentEmptinessMerge

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness
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
variable {EnumGuard : Type} {width : Nat}

/-- Retain the optional node and reject its empty handle before writes. -/
def finishOptional (source target : Nat) (node : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) :
    EnumerateM Symbol EnumGuard Unit :=
  fun state =>
    if node = some 0 then [] else
      [.ok ((), assimilated state target source (.unenumerated node (sourceScs ++ targetScs)))]

/-- Keep the reached caller and query pair outside a missing encoded action. -/
noncomputable def afterQuery
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (p h : Nat) (source target : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (query : Node) (queried : Checked width) (beforeCaller : Caller width) (queries : Queries) :
    (Except (SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (EnumerateM Symbol EnumGuard Unit))) × Caller width × Queries :=
  let phase : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
    if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (.done false queried beforeCaller.fourth, queries)
  match phase.1 with
  | .done answer checkedAfter saved =>
      let replacement : Node := if answer then .empty else query
      (.ok ((encodeNode replacement).map (fun handle =>
          SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement)),
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)
  | .failed _ checkedAfter saved =>
      (.error phase.1,
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)

/-- Select the source branches before the actual checked query and enabled check. -/
noncomputable def dispatch
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (EnumerateM Symbol EnumGuard Unit))) × Caller width × Queries := Id.run do
  let noop : EnumerateM Symbol EnumGuard Unit := fun state => [.ok ((), state)]
  if source = target then return (.ok (some noop), beforeCaller, queries)
  let some sourceValue := before.values[source]? | return (.ok none, beforeCaller, queries)
  match sourceValue with
  | .eliminated => return (.ok (some noop), beforeCaller, queries)
  | _ => pure PUnit.unit
  let some targetValue := before.values[target]? | return (.ok none, beforeCaller, queries)
  let .unenumerated sourceNode sourceScs := sourceValue |
    return (.ok (some (failure .invalidIntersection)), beforeCaller, queries)
  let .unenumerated targetNode targetScs := targetValue |
    return (.ok (some (failure .invalidIntersection)), beforeCaller, queries)
  let some sourceHandle := sourceNode |
    return (.ok (some (finishOptional source target targetNode sourceScs targetScs)), beforeCaller, queries)
  let some targetHandle := targetNode |
    return (.ok (some (finishOptional source target (some sourceHandle) sourceScs targetScs)), beforeCaller, queries)
  let some left := lookupNode beforeCaller.checked.native.machine.heap sourceHandle |
    return (.ok none, beforeCaller, queries)
  let some right := lookupNode beforeCaller.checked.native.machine.heap targetHandle |
    return (.ok none, beforeCaller, queries)
  let actual : SourceEqualityNativeDemand.Outcome width Node :=
    SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked
  match actual with
  | .done query queried =>
    let prepared :
      (Except (SourceCurrentAllocatedConjunctionWorker.Outcome width)
        (Option (EnumerateM Symbol EnumGuard Unit))) × Caller width × Queries :=
      afterQuery checkEmpty p h source target sourceScs targetScs query queried beforeCaller queries
    return (prepared.1.mapError Sum.inr, prepared.2.1, prepared.2.2)
  | other => return (.error (.inl other),
      SourceCurrentAllocatedPartialState.advance beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries)

/-- Safe raw entries derive the same finite dispatcher and exact enumeration result. -/
theorem dispatch_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (source target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (slots : source = target ∨ before.values[source]? = some .eliminated ∨
      ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
        before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.values[target]? = some (.unenumerated targetNode targetScs))
    (ranges : if source = target then True else
      match before.values[source]?, before.values[target]? with
      | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap left,
              lookupNode beforeCaller.checked.native.machine.heap right with
          | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
              beforeCaller.checked
          | _, _ => True
      | _, _ => True) :
    ∃ (fuel p h : Nat) (action : EnumerateM Symbol EnumGuard Unit)
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra P H, p ≤ P → h ≤ H →
        dispatch checkEmpty (fuel + extra) P H beforeCaller before source target memos.query =
          (.ok (some action), afterCaller, savedQueries)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      PendingRealized afterCaller.checked.native.machine.heap before ∧
      ((source = target ∨ before.values[source]? = some .eliminated) →
        ExceptT.run (action before) = [.ok ((), before)] ∧
        afterCaller = beforeCaller ∧ final = memos ∧ next = inventory) ∧
      (source ≠ target → before.values[source]? ≠ some .eliminated →
        ∃ (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
          before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
          before.values[target]? = some (.unenumerated targetNode targetScs) ∧
          ExceptT.run (action before) =
            (if merged = some 0 then [] else
              [.ok ((), assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)))]) ∧
          (merged ≠ some 0 →
            (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[target]? =
              some (.unenumerated merged (sourceScs ++ targetScs)) ∧
            (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[source]? =
              some .eliminated ∧
            PendingRealized afterCaller.checked.native.machine.heap
              (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)))) ∧
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
  have optionalPacket :
    ∀ (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
      before.values[source]? = some (.unenumerated sourceNode sourceScs) →
      before.values[target]? = some (.unenumerated targetNode targetScs) →
      source ≠ target → (sourceNode = none ∨ targetNode = none) →
      merged = sourceNode.orElse (fun _ => targetNode) →
      ExceptT.run (finishOptional (EnumGuard := EnumGuard) source target merged sourceScs targetScs before) =
        (if merged = some 0 then [] else
          [.ok ((), assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)))]) ∧
      (merged ≠ some 0 →
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[target]? =
          some (.unenumerated merged (sourceScs ++ targetScs)) ∧
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[source]? =
          some .eliminated ∧
        PendingRealized beforeCaller.checked.native.machine.heap
          (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)))) := by
    intro sourceNode targetNode merged sourceScs targetScs sourceStored targetStored different _missing carried
    have sourceInside : source < before.values.length := by
      exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound _storedValue => bound)
    have targetInside : target < before.values.length := by
      exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound _storedValue => bound)
    have carriedRealized :
      ∀ (slot node : Nat) (scs : List EnumerationState.Suspended),
        (before.values.set target (.unenumerated merged (sourceScs ++ targetScs)))[slot]? =
          some (.unenumerated (some node) scs) →
        ∃ value : Node, lookupNode beforeCaller.checked.native.machine.heap node = some value ∧
          Available beforeCaller.checked.native.machine.heap value ∧ value.free = [] := by
      intro slot node scs stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact realized oldSlot node scs oldStored
      · cases sourceNode with
        | none =>
            simp only [Option.orElse_none] at carried
            rw [← carried, ← (UVarValue.unenumerated.inj fresh).1] at targetStored
            exact realized target node targetScs targetStored
        | some sourceHandle =>
            simp only [Option.orElse_some] at carried
            rw [← carried, ← (UVarValue.unenumerated.inj fresh).1] at sourceStored
            exact realized source node sourceScs sourceStored
    refine ⟨rfl, ?_⟩
    intro nonzero
    refine ⟨?_, ?_, ?_⟩
    · simpa only [assimilated, List.getElem?_set_ne different] using
        (List.getElem?_set_self (a := UVarValue.unenumerated merged (sourceScs ++ targetScs)) targetInside)
    · exact List.getElem?_set_self (by simpa only [List.length_set] using sourceInside)
    · intro slot node scs stored
      change ((before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set
        source .eliminated)[slot]? = some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact carriedRealized oldSlot node scs oldStored
      · cases fresh
  have presentPacket :
    ∀ (sourceHandle targetHandle : Nat) (sourceScs targetScs : List EnumerationState.Suspended),
      before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs) →
      before.values[target]? = some (.unenumerated (some targetHandle) targetScs) → source ≠ target →
      ∃ (left right query replacement : Node) (queried : Checked width) (handle : Nat)
        (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory) (p h : Nat),
        lookupNode beforeCaller.checked.native.machine.heap sourceHandle = some left ∧
        lookupNode beforeCaller.checked.native.machine.heap targetHandle = some right ∧
        next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
        SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
          beforeCaller.checked query queried memos ∧
        (∀ P H, p ≤ P → h ≤ H →
          afterQuery checkEmpty P H source target sourceScs targetScs query queried beforeCaller memos.query =
            (.ok (some (SourcePruningEnumerationAssimilation.finish (EnumGuard := EnumGuard)
              source target handle sourceScs targetScs replacement)), afterCaller, savedQueries)) ∧
        Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
        PendingRealized afterCaller.checked.native.machine.heap before ∧
        encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
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
                SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final)) := by
    intro sourceHandle targetHandle sourceScs targetScs sourceStored targetStored _different
    have pairRanges :
        match lookupNode beforeCaller.checked.native.machine.heap sourceHandle,
            lookupNode beforeCaller.checked.native.machine.heap targetHandle with
        | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
            beforeCaller.checked
        | _, _ => True := by
      simpa only [ite_eq_right _different, sourceStored, targetStored] using ranges
    cases checkEmpty with
    | false =>
      obtain ⟨left, leftDecoded, leftAvailable, leftClosed⟩ := realized source sourceHandle sourceScs sourceStored
      obtain ⟨right, rightDecoded, rightAvailable, rightClosed⟩ := realized target targetHandle targetScs targetStored
      have decodedRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked := by
        simpa only [leftDecoded, rightDecoded] using pairRanges
      obtain ⟨next, query, queried, nextSource, nextRoots, receipt⟩ :=
        SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
          initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed decodedRanges memos initial.globals
      have queryProbes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap := by
        cases receipt.actual with
        | @run traceFuel trace =>
            exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
      have queryContext : Context formulas solver next
        (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge) memos := by
        exact ⟨receipt.ready, receipt.admitted,
          initial.sound.advance formulas solver queried beforeCaller.fourth beforeCaller.merge receipt.effects,
          initial.stored.grows receipt.effects.keeps, initial.covered,
          SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps beforeCaller.fourth initial.correct,
          receipt.globals, queryProbes⟩
      have queryPost : Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge) memos := by
        exact ⟨queryContext, receipt.effects, Cache.extends_refl _, (Post.refl initial).fourthRetained⟩
      obtain ⟨handle, encoded, decoded⟩ := available_readback queried.native.machine.heap query
        receipt.effects.keeps.ready.semantic.1.normal.facts.coherent receipt.available receipt.closed
      have finalRealized : PendingRealized queried.native.machine.heap before := by
        exact realized_preserved beforeCaller.checked.native.machine.heap queried.native.machine.heap
          before before realized (EnumerationCompressionFrame.Frame.refl before) receipt.effects.keeps
      refine ⟨left, right, query, query, queried, handle,
        SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge,
        memos.query, memos, next, 0, 0, leftDecoded, rightDecoded, nextSource, nextRoots, receipt,
        ?_, queryPost, rfl, finalRealized, encoded, decoded, receipt.available, receipt.closed, receipt.meaning, ?_, ?_⟩
      · intro P H enoughP enoughH
        simp only [afterQuery, Bool.false_eq_true, ↓reduceIte, encoded, Option.map_some]
      · intro _
        exact ⟨rfl, rfl, rfl⟩
      · intro impossible
        cases impossible
    | true =>
      obtain ⟨left, right, next, query, queried, reached, answer, guardSaved, checkedAfter, saved,
        final, replacement, handle, p, h, leftDecoded, rightDecoded, nextSource, nextRoots,
        receipt, guardRun, guardChecked, stable, post, skipped, performed, sound, unfolding,
        querySame, replacementSame, available, closed, encoded, decoded, preRealized, meaning⟩ :=
        SourcePruningEnumerationEnabledEmpty.pending_enabled_complete formulas solver inventory beforeCaller
          before source target sourceHandle targetHandle sourceScs targetScs memos initial realized
          sourceStored targetStored pairRanges
      refine ⟨left, right, query, replacement, queried, handle,
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge,
        guardSaved, final, next, p, h, leftDecoded, rightDecoded, nextSource, nextRoots,
        receipt, ?_, post, querySame, preRealized, encoded, decoded, available, closed, meaning, ?_, ?_⟩
      · intro P H enoughP enoughH
        simp only [afterQuery, ↓reduceIte, stable P H enoughP enoughH,
          ← replacementSame, encoded, Option.map_some]
      · intro impossible
        cases impossible
      · intro _
        exact ⟨reached, answer, guardSaved, guardRun, guardChecked, stable, rfl, replacementSame, skipped, performed⟩
  by_cases same : source = target
  · refine ⟨0, 0, 0, (fun state => [.ok ((), state)]), beforeCaller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, ite_eq_left same, Id.run]; rfl
    · intro noWork
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro different notEliminated
      exact False.elim (different same)
  by_cases eliminated : before.values[source]? = some .eliminated
  · refine ⟨0, 0, 0, (fun state => [.ok ((), state)]), beforeCaller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, ite_eq_right same, eliminated, Id.run]; rfl
    · intro noWork
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro different notEliminated
      exact False.elim (notEliminated eliminated)
  rcases (slots.resolve_left same).resolve_left eliminated with
    ⟨sourceNode, targetNode, sourceScs, targetScs, sourceStored, targetStored⟩
  by_cases missing : sourceNode = none ∨ targetNode = none
  ·
    let merged : Option Nat := sourceNode.orElse (fun _ => targetNode)
    refine ⟨0, 0, 0, finishOptional source target merged sourceScs targetScs,
      beforeCaller, memos.query, memos, inventory, ?_, Post.refl initial, rfl, realized, ?_, ?_⟩
    · intro extra P H enoughP enoughH
      simp only [dispatch, ite_eq_right same, sourceStored, targetStored]
      cases sourceNode with
      | none => rfl
      | some sourceHandle =>
          cases targetNode with
          | none => rfl
          | some targetHandle => cases missing <;> contradiction
    · intro noWork
      exact False.elim (noWork.elim same eliminated)
    · intro different notEliminated
      refine ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
        (optionalPacket sourceNode targetNode merged sourceScs targetScs sourceStored targetStored same missing rfl).1,
        (optionalPacket sourceNode targetNode merged sourceScs targetScs sourceStored targetStored same missing rfl).2, ?_, ?_⟩
      · intro _
        exact ⟨rfl, rfl, rfl, rfl⟩
      · intro leftHandle rightHandle leftSame rightSame
        rcases missing with sourceMissing | targetMissing
        · rw [sourceMissing] at leftSame
          cases leftSame
        · rw [targetMissing] at rightSame
          cases rightSame
  cases sourceNode with
  | none => exact False.elim (missing (.inl rfl))
  | some sourceHandle =>
    cases targetNode with
    | none => exact False.elim (missing (.inr rfl))
    | some targetHandle =>
      obtain ⟨left, right, query, replacement, queried, handle, afterCaller, savedQueries, final, next, p, h,
        leftDecoded, rightDecoded, nextSource, nextRoots, receipt, phaseStable, post, querySame,
        preRealized, encoded, decoded, available, closed, meaning, disabled, enabled⟩ :=
        presentPacket sourceHandle targetHandle sourceScs targetScs sourceStored targetStored same
      obtain ⟨fuel, actualDone⟩ := receipt.actual.done
      obtain ⟨emptyRaw, nonemptyRaw⟩ := SourcePruningEnumerationFinish.finish_complete
        afterCaller.checked.native.machine.heap before replacement source target sourceHandle targetHandle handle
        sourceScs targetScs post.effects.keeps.ready.semantic.1.normal.facts.coherent
        available closed encoded preRealized sourceStored targetStored (Ne.symm same)
      have emptyIff : replacement = .empty ↔ handle = 0 := by
        constructor
        · intro isEmpty
          simpa only [isEmpty, encodeNode, Option.some.injEq] using encoded.symm
        · intro isZero
          simpa only [isZero, lookupNode, Option.some.injEq] using decoded.symm
      refine ⟨fuel, p, h, SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement,
        afterCaller, savedQueries, final, next, ?_, post, querySame, preRealized, ?_, ?_⟩
      · intro extra P H enoughP enoughH
        simp only [dispatch, ite_eq_right same, sourceStored, targetStored, leftDecoded, rightDecoded,
          SourceEqualityNativeDemand.done_stable fuel extra _ beforeCaller.checked queried query actualDone,
          phaseStable P H enoughP enoughH, Except.mapError, Id.run]; rfl
      · intro noWork
        exact False.elim (noWork.elim same eliminated)
      · intro different notEliminated
        refine ⟨some sourceHandle, some targetHandle, some handle, sourceScs, targetScs,
          sourceStored, targetStored, ?_, ?_, ?_, ?_⟩
        · by_cases isEmpty : replacement = .empty
          · simpa only [ite_eq_left (congrArg some (emptyIff.mp isEmpty))] using emptyRaw isEmpty
          · obtain ⟨after, raw, afterSame, targetRead, sourceRead, afterRealized⟩ := nonemptyRaw isEmpty
            subst after
            simpa only [ite_eq_right (fun zero => isEmpty (emptyIff.mpr (Option.some.inj zero)))] using raw
        · intro nonzero
          obtain ⟨after, raw, afterSame, targetRead, sourceRead, afterRealized⟩ :=
            nonemptyRaw (fun isEmpty => nonzero (congrArg some (emptyIff.mp isEmpty)))
          subst after
          exact ⟨targetRead, sourceRead, afterRealized⟩
        · intro optional
          rcases optional with absent | absent <;> cases absent
        · intro leftHandle rightHandle leftSame rightSame
          cases Option.some.inj leftSame
          cases Option.some.inj rightSame
          exact ⟨left, right, query, replacement, queried, handle, leftDecoded, rightDecoded,
            nextSource, nextRoots, receipt, rfl, encoded, decoded, available, closed, meaning, disabled, enabled⟩

end MicroCFTA.SourcePruningEnumerationDispatch
