import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationPendingWriteLanguage

/-!
# Assignment meaning of the actual incoming cache adapter

The original producer runs once. Its full receipt remains available.
The Empty candidate denotes the logical write. The runtime branch list stays empty.
A nonempty branch contains the same written core as the attached cache.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationExecution EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Retain every cache receipt and interpret the logical core and actual branch list. -/
theorem complete_semantics
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (target : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (roots : Nat → Nat)
    (initial : Context formulas solver inventory beforeCaller memos)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (root : IsRoot before.core.representatives target)
    (pending : EnumerationCompleteness.PendingAt before.core target)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (ranges : match before.core.values[target]? with
      | some (.unenumerated (some oldHandle) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              beforeCaller.checked
          | none => True
      | _ => True) :
    ∃ (r n p h k : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read : EnumerationState.State Symbol Constraint) (afterCaller : Caller width)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (replacement : Node) (handle : Nat)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra, ExceptT.run (getValue (r + extra) target before.core) =
        [.ok (.unenumerated oldNode oldScs, read)]) ∧
      EnumerationCompressionFrame.Frame before.core read ∧
      (∀ extra extraNative P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationIncomingNode.run checkEmpty (r + extra) (n + extraNative) P H
          beforeCaller before.core target incoming incomingScs memos.query =
          (.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
            afterCaller, savedQueries, read)) ∧
      ExceptT.run ((do
        setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry target) read) = [.ok ((), after.core)] ∧
      after.core = {read with
        values := read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (read.expansionAncestry ++ read.recursionAncestry target).eraseDups else read.recursionAncestry other} ∧
      after.core.values[target]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Cache.Extends memos.unfolding final.unfolding ∧
      Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
      (∀ extra, (SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
        (k + extra) target (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
        (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame after.core) = some after) ∧
      (∀ extraIndex, adapt afterCaller.checked.native.machine.heap (k + extraIndex) target
        incomingScs before read (if replacement = .empty then [] else [.ok ((), after.core)]) = some after) ∧
      (∀ extra extraNative P H extraIndex, p ≤ P → h ≤ H →
        run checkEmpty (r + extra) (n + extraNative) P H (k + extraIndex)
          beforeCaller before target incoming incomingScs memos.query =
          ((.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
            afterCaller, savedQueries, read), some after)) ∧
      after.core.counter = before.core.counter ∧ after.core.representatives = read.representatives ∧
      Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      after.expandable = (fun slot => if slot = target then
        !(MergedOrdinaryHeight.recursiveBoundary replacement && (incomingScs ++ oldScs).isEmpty)
        else before.expandable slot) ∧
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
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment target) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment target) sc) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        (∃ output : EnumerationState.State Symbol Constraint,
          Except.ok ((), output) ∈
            (if replacement = .empty then [] else [.ok ((), after.core)] : Raw) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient incoming (assignment target) ∧
          ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment target) sc := by
  obtain ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, adapted, wrapperRun, afterCounter,
    afterRepresentatives, afterPaths, afterCounts, waiting, flagsAfter, expandableAfter,
    optional, present⟩ :=
      complete formulas solver inventory beforeCaller before checkEmpty target incoming incomingScs
        memos roots initial storage realized paths counts flags root pending available closed bounded ranges
  have readSuccess : Success (getValue r target) before.core (.unenumerated oldNode oldScs) read := by
    have actual := reading 0
    simp only [Nat.add_zero] at actual
    rw [Success, actual]
    exact List.mem_singleton_self _
  obtain ⟨_, found, _size, beforePath, _, oldStored⟩ :=
    getValue_frame r target before.core read (.unenumerated oldNode oldScs) storage.total readSuccess
  obtain ⟨_rootSize, rootPath⟩ := root
  have foundSame : found = target := (UnionFind.reaches_unique beforePath rootPath).1
  have beforeStored : before.core.values[target]? = some (.unenumerated oldNode oldScs) := by
    simpa only [foundSame] using oldStored
  have readStored : read.values[target]? = some (.unenumerated oldNode oldScs) := by
    simpa only [frame.values] using beforeStored
  have logical : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming (assignment target) ∧
        ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment target) sc := by
    intro ambient residualMeaning assignment
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
          obtain ⟨same, _⟩ := optional oldCase
          simp only [Option.map_none, Fragments.permits, same, and_true]
      | some oldHandle =>
          obtain ⟨old, _queryNode, _queried, oldDecoded, _, _, _, exactMeaning, _⟩ := present oldHandle oldCase
          have keptDecoded := lookupNode_keeps beforeCaller.checked.native.machine.heap
            afterCaller.checked.native.machine.heap post.effects.keeps oldHandle old oldDecoded
          simpa only [oldCase, Option.map_some, Fragments.permits,
            SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ keptDecoded] using
              exactMeaning ambient term
    have writeMeaning := SourcePruningEnumerationPendingWriteLanguage.pending_write
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap) residualMeaning assignment read after.core target handle
      oldNode oldScs incomingScs
      (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming)
      readStored (by rw [afterSame]) (by rw [afterSame]) (by rw [afterSame]) replacementMeaning
    have readMeaning := SourcePruningEnumerationNativeLanguage.satisfies_keeps_frame
      (SourceEqualityPCSGuard.holds formulas solver) ambient beforeCaller.checked.native.machine.heap
      afterCaller.checked.native.machine.heap before.core read residualMeaning assignment realized frame post.effects.keeps
    exact writeMeaning.trans (and_congr_left fun _ => readMeaning)
  refine ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, adapted, wrapperRun, afterCounter,
    afterRepresentatives, afterPaths, afterCounts, waiting, flagsAfter, expandableAfter,
    optional, present, logical, ?_⟩
  intro ambient residualMeaning assignment
  have replacementHolds
      (satisfied : Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core) :
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient replacement (assignment target) := by
    have atSlot := satisfied.1.2 target
    change Fragments.slotSatisfies assignment target
      (slot (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient afterCaller.checked.native.machine.heap)
          ((after.core.values[target]?).getD .eliminated)) at atSlot
    rw [afterStored] at atSlot
    change (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap handle (assignment target) ∧ _) at atSlot
    exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp atSlot.1
  have rawLogical :
      (∃ output : EnumerationState.State Symbol Constraint,
        Except.ok ((), output) ∈
          (if replacement = .empty then [] else [.ok ((), after.core)] : Raw) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core := by
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
        have pairSame : ((), output) = ((), after.core) := Except.ok.inj (List.mem_singleton.mp member)
        have outputSame : output = after.core := congrArg Prod.snd pairSame
        simpa only [outputSame] using satisfied
      · intro satisfied
        exact ⟨after.core, List.mem_singleton_self _, satisfied⟩
  exact rawLogical.trans (logical ambient residualMeaning assignment)

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
