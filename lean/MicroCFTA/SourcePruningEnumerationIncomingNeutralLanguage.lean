import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationNeutralLanguage

/-!
# Neutral assignment meaning of the actual incoming-node update

The producer runs once. Its complete original receipt is retained.
The logical write adds the incoming node and its suspended constraints.
A separate captured payload stays neutral throughout this same receipt.
An Empty replacement still has a logical receipt. The actual runtime
returns an empty branch list in that case.
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

/-- The actual incoming producer retains every receipt and proves exact logical assignment meaning. -/
theorem run_complete_neutral_semantics
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
      ∀ (held : Nat), uv ≠ held →
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held after) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before) ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment uv) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment uv) sc := by
  obtain ⟨r, n, p, h, oldNode, oldScs, read, after, afterCaller, savedQueries, final, next,
    replacement, handle, reading, frame, running, writing, afterSame, stored, afterStorage,
    afterRealized, post, query, unfolding, replacementAvailable, replacementClosed, encoded,
    decoded, noOld, hasOld⟩ :=
    run_complete formulas solver inventory beforeCaller before checkEmpty uv incoming incomingScs memos
      initial realized storage root pending available closed bounded ranges
  refine ⟨r, n, p, h, oldNode, oldScs, read, after, afterCaller, savedQueries, final, next,
    replacement, handle, reading, frame, running, writing, afterSame, stored, afterStorage,
    afterRealized, post, query, unfolding, replacementAvailable, replacementClosed, encoded,
    decoded, noOld, hasOld, ?_⟩
  intro held different ambient residualMeaning assignment
  have readSuccess : Success (getValue r uv) before (.unenumerated oldNode oldScs) read := by
    have actual := reading 0
    simp only [Nat.add_zero] at actual
    rw [Success, actual]
    exact List.mem_singleton_self _
  obtain ⟨_, found, _size, beforePath, _, oldStored⟩ :=
    getValue_frame r uv before read (.unenumerated oldNode oldScs) storage.total readSuccess
  obtain ⟨_rootSize, rootPath⟩ := root
  have foundSame : found = uv := (UnionFind.reaches_unique beforePath rootPath).1
  have beforeStored : before.values[uv]? = some (.unenumerated oldNode oldScs) := by
    simpa only [foundSame] using oldStored
  have readStored : read.values[uv]? = some (.unenumerated oldNode oldScs) := by
    simpa only [frame.values] using beforeStored
  have replacementMeaning : ∀ term,
      SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap handle term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
        Fragments.permits
          (oldNode.map (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient afterCaller.checked.native.machine.heap)) term := by
    intro term
    rw [SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded]
    cases oldCase : oldNode with
    | none =>
        obtain ⟨same, _⟩ := noOld oldCase
        simp only [Option.map_none, Fragments.permits, same, and_true]
    | some oldHandle =>
        obtain ⟨old, _queryNode, _queried, oldDecoded, _, _, _, exactMeaning, _⟩ := hasOld oldHandle oldCase
        have keptDecoded := lookupNode_keeps beforeCaller.checked.native.machine.heap
          afterCaller.checked.native.machine.heap post.effects.keeps oldHandle old oldDecoded
        simpa only [oldCase, Option.map_some, Fragments.permits,
          SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ keptDecoded] using
          exactMeaning ambient term
  have writeMeaning := SourcePruningEnumerationNeutralLanguage.pending_write_neutral
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap) residualMeaning assignment read after held uv handle
    oldNode oldScs incomingScs
    (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming)
    readStored different (by rw [afterSame]) (by rw [afterSame]) (by rw [afterSame]) replacementMeaning
  have readMeaning := SourcePruningEnumerationNeutralLanguage.satisfies_neutral_keeps_frame
    (SourceEqualityPCSGuard.holds formulas solver) ambient beforeCaller.checked.native.machine.heap
    afterCaller.checked.native.machine.heap before read held residualMeaning assignment realized frame post.effects.keeps
  exact writeMeaning.trans (and_congr_left fun _ => readMeaning)

end MicroCFTA.SourcePruningEnumerationIncomingNode
