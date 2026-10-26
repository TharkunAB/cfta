import MicroCFTA.SourcePruningEnumerationIncomingNodeLanguage

/-!
# Complete assignments represented by actual incoming branches

The original producer runs once. Its full logical receipt remains available.
The actual Empty branch has no satisfying assignment at the written slot.
A nonempty raw singleton retains the same logical written core.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
open EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation SourcePruningEnumerationWrites
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Retain every incoming receipt and interpret the actual rejecting or singleton branch list. -/
theorem run_complete_branches
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (storage : StorageValid before) (root : EnumerationSchedule.IsRoot before.representatives uv)
    (pending : EnumerationCompleteness.PendingAt before uv)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : match before.values[uv]? with
      | some (.unenumerated (some oldHandle) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              beforeCaller.checked
          | none => True
      | _ => True) :
    ∃ (r n p h : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read after : EnumerationState.State Symbol EnumGuard) (afterCaller : Caller width)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (replacement : Node) (handle : Nat),
      (∀ extra, ExceptT.run (getValue (r + extra) uv before) =
        [.ok (.unenumerated oldNode oldScs, read)]) ∧
      EnumerationCompressionFrame.Frame before read ∧
      (∀ extra extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extra) (n + extraNative) P H beforeCaller before uv incoming incomingScs memos.query =
          (.ok (some (if replacement = .empty then [] else [.ok ((), after)])),
            afterCaller, savedQueries, read)) ∧
      ExceptT.run ((do
        setValue uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry uv) read) = [.ok ((), after)] ∧
      after = {read with
        values := read.values.set uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = uv then
          (read.expansionAncestry ++ read.recursionAncestry uv).eraseDups else read.recursionAncestry other} ∧
      after.values[uv]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after ∧ PendingRealized afterCaller.checked.native.machine.heap after ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Cache.Extends memos.unfolding final.unfolding ∧
      Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
      (oldNode = none → replacement = incoming ∧ afterCaller = beforeCaller ∧
        savedQueries = memos.query ∧ final = memos ∧ next = inventory) ∧
      (∀ oldHandle, oldNode = some oldHandle →
        ∃ (old query : Node) (queried : Checked width),
          lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old ∧
          next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [incoming, old] ∧
          SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old beforeCaller.checked query queried memos ∧
          (∀ ambient term,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
          (checkEmpty = false → replacement = query ∧
            afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge ∧
            final = memos)) ∧
      (∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment uv) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment uv) sc) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        (∃ output : EnumerationState.State Symbol EnumGuard,
          Except.ok ((), output) ∈
            (if replacement = .empty then [] else [.ok ((), after)] :
              List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment uv) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment uv) sc := by
  obtain ⟨r, n, p, h, oldNode, oldScs, read, after, afterCaller, savedQueries, final, next,
    replacement, handle, reading, frame, running, writing, afterSame, stored, afterStorage,
    afterRealized, post, query, unfolding, replacementAvailable, replacementClosed, encoded,
    decoded, noOld, hasOld, logical⟩ :=
    run_complete_semantics formulas solver inventory beforeCaller before checkEmpty uv incoming incomingScs memos
      initial realized storage root pending available closed bounded ranges
  refine ⟨r, n, p, h, oldNode, oldScs, read, after, afterCaller, savedQueries, final, next,
    replacement, handle, reading, frame, running, writing, afterSame, stored, afterStorage,
    afterRealized, post, query, unfolding, replacementAvailable, replacementClosed, encoded,
    decoded, noOld, hasOld, logical, ?_⟩
  intro ambient residualMeaning assignment
  have replacementHolds
      (satisfied : Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after) :
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient replacement (assignment uv) := by
    have atSlot := satisfied.1.2 uv
    change Fragments.slotSatisfies assignment uv
      (slot (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap)
          ((after.values[uv]?).getD .eliminated)) at atSlot
    rw [stored] at atSlot
    change (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap handle (assignment uv) ∧ _) at atSlot
    exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp atSlot.1
  have rawLogical :
      (∃ output : EnumerationState.State Symbol EnumGuard,
        Except.ok ((), output) ∈
          (if replacement = .empty then [] else [.ok ((), after)] :
            List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after := by
    by_cases empty : replacement = .empty
    · constructor
      · rintro ⟨output, member, _satisfied⟩
        simp only [ite_eq_left empty, List.not_mem_nil] at member
      · intro satisfied
        have impossible := replacementHolds satisfied
        rw [empty, InternedGuardedLanguage.meaning] at impossible
        exact False.elim impossible
    · rw [ite_eq_right empty]
      constructor
      · rintro ⟨output, member, satisfied⟩
        have pairSame : ((), output) = ((), after) := Except.ok.inj (List.mem_singleton.mp member)
        have outputSame : output = after := congrArg Prod.snd pairSame
        simpa only [outputSame] using satisfied
      · intro satisfied
        exact ⟨after, List.mem_singleton_self _, satisfied⟩
  exact rawLogical.trans (logical ambient residualMeaning assignment)

end MicroCFTA.SourcePruningEnumerationIncomingNode
