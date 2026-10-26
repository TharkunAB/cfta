import MicroCFTA.SourcePruningEnumerationDispatch
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationAssimilationLanguage

/-!
# Assignment meaning of the actual pending-slot dispatcher

The original producer runs once. Its full receipt remains available.
The semantic clause requires the original forest to equate source and target.
The Empty branch rejects every complete assignment. A nonempty branch retains it.
-/
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

/-- Retain every dispatcher receipt and interpret its actual branch list under the original class equality. -/
theorem dispatch_complete_semantics
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
                      SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := guardSaved} final)))) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        UnionFind.SameClass before.representatives source target →
          ((∃ after : EnumerationState.State Symbol EnumGuard,
            Except.ok ((), after) ∈ ExceptT.run (action before) ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after) ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before) := by
  obtain ⟨fuel, p, h, action, afterCaller, savedQueries, final, next,
    running, post, querySame, afterRealized, noop, live⟩ :=
      dispatch_complete formulas solver inventory beforeCaller before checkEmpty source target memos
        initial realized slots ranges
  refine ⟨fuel, p, h, action, afterCaller, savedQueries, final, next,
    running, post, querySame, afterRealized, noop, live, ?_⟩
  intro ambient residualMeaning assignment sameClass
  by_cases noWork : source = target ∨ before.values[source]? = some .eliminated
  · obtain ⟨raw, callerSame, _finalSame, _nextSame⟩ := noop noWork
    rw [raw, callerSame]
    constructor
    · rintro ⟨after, member, satisfied⟩
      have pairSame : ((), after) = ((), before) := Except.ok.inj (List.mem_singleton.mp member)
      have afterSame : after = before := congrArg Prod.snd pairSame
      simpa only [afterSame] using satisfied
    · intro satisfied
      exact ⟨before, List.mem_singleton_self _, satisfied⟩
  · have different : source ≠ target := fun same => noWork (.inl same)
    have notEliminated : before.values[source]? ≠ some .eliminated := fun same => noWork (.inr same)
    obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs,
      sourceStored, targetStored, actionRaw, _survives, optional, present⟩ := live different notEliminated
    let language : NodeLanguage Symbol :=
      SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap
    have replacementPermits : ∀ term,
        Fragments.permits (merged.map language) term ↔
          Fragments.permits (sourceNode.map language) term ∧
          Fragments.permits (targetNode.map language) term := by
      intro term
      cases sourceNode with
      | none =>
          obtain ⟨carried, _callerSame, _finalSame, _nextSame⟩ := optional (.inl rfl)
          simp only [Option.orElse_none] at carried
          simp only [carried, Option.map_none, Fragments.permits, true_and]
      | some leftHandle =>
          cases targetNode with
          | none =>
              obtain ⟨carried, _callerSame, _finalSame, _nextSame⟩ := optional (.inr rfl)
              simp only [Option.orElse_some] at carried
              simp only [carried, Option.map_none, Fragments.permits, and_true]
          | some rightHandle =>
              obtain ⟨left, right, _queryNode, replacement, _queried, handle,
                leftDecoded, rightDecoded, _nextSource, _nextRoots, _receipt,
                mergedSame, _encoded, decoded, _available, _closed, exactMeaning,
                _disabled, _enabled⟩ := present leftHandle rightHandle rfl rfl
              have leftKept := lookupNode_keeps beforeCaller.checked.native.machine.heap
                afterCaller.checked.native.machine.heap post.effects.keeps leftHandle left leftDecoded
              have rightKept := lookupNode_keeps beforeCaller.checked.native.machine.heap
                afterCaller.checked.native.machine.heap post.effects.keeps rightHandle right rightDecoded
              simpa only [mergedSame, Option.map_some, Fragments.permits, language,
                SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded,
                SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ leftKept,
                SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ rightKept] using
                  exactMeaning ambient term
    have logical := SourcePruningEnumerationAssimilationLanguage.assimilated_semantics
      language residualMeaning assignment before source target sourceNode targetNode merged
      sourceScs targetScs sourceStored targetStored different sameClass replacementPermits
    have oldMeaning := SourcePruningEnumerationNativeLanguage.satisfies_keeps
      (SourceEqualityPCSGuard.holds formulas solver) ambient beforeCaller.checked.native.machine.heap
      afterCaller.checked.native.machine.heap before residualMeaning assignment realized post.effects.keeps
    have targetInside : target < before.values.length := (List.getElem?_eq_some_iff.mp targetStored).1
    have targetWritten :
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[target]? =
          some (.unenumerated merged (sourceScs ++ targetScs)) := by
      simpa only [assimilated, List.getElem?_set_ne different] using
        (List.getElem?_set_self (a := UVarValue.unenumerated merged (sourceScs ++ targetScs)) targetInside)
    have rawLogical :
        (∃ after : EnumerationState.State Symbol EnumGuard,
          Except.ok ((), after) ∈ ExceptT.run (action before) ∧
          Satisfies language residualMeaning assignment after) ↔
        Satisfies language residualMeaning assignment
          (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
      rw [actionRaw]
      by_cases empty : merged = some 0
      · constructor
        · rintro ⟨after, member, _satisfied⟩
          simp only [ite_eq_left empty, List.not_mem_nil] at member
        · intro satisfied
          have atSlot := satisfied.1.2 target
          change Fragments.slotSatisfies assignment target
            (slot language
              (((assimilated before target source
                (.unenumerated merged (sourceScs ++ targetScs))).values[target]?).getD .eliminated)) at atSlot
          rw [targetWritten] at atSlot
          change (Fragments.permits (merged.map language) (assignment target) ∧ _) at atSlot
          have holdsZero : language 0 (assignment target) := by
            simpa only [empty, Option.map_some, Fragments.permits] using atSlot.1
          have impossible :=
            (SourcePruningEnumerationNativeLanguage.handles_lookup
              (SourceEqualityPCSGuard.holds formulas solver) ambient
              afterCaller.checked.native.machine.heap 0 .empty (assignment target) rfl).mp holdsZero
          rw [InternedGuardedLanguage.meaning] at impossible
          exact False.elim impossible
      · rw [ite_eq_right empty]
        constructor
        · rintro ⟨after, member, satisfied⟩
          have pairSame : ((), after) = ((), assimilated before target source
              (.unenumerated merged (sourceScs ++ targetScs))) :=
            Except.ok.inj (List.mem_singleton.mp member)
          have afterSame := congrArg Prod.snd pairSame
          simpa only [afterSame] using satisfied
        · intro satisfied
          exact ⟨assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)),
            List.mem_singleton_self _, satisfied⟩
    exact rawLogical.trans (logical.trans oldMeaning)

end MicroCFTA.SourcePruningEnumerationDispatch
