import MicroCFTA.SourcePruningEnumerationNativeIndex

namespace MicroCFTA.SourcePruningEnumerationCachedIncoming
open EnumerationState EnumerationSchedule EnumerationCorrectness
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
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- The existing incoming action derives the logical cache of its actual write. -/
theorem complete
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
            final = memos)) := by
  obtain ⟨r, n, p, h, oldNode, oldScs, read, afterCore, afterCaller, savedQueries,
    final, next, replacement, handle, reading, frame, runStable, writePrefix,
    coreSame, storedAfter, afterStorage, afterRealized, post, querySame, unfolding,
    replacementAvailable, replacementClosed, encoded, decoded, optional, present⟩ :=
    SourcePruningEnumerationIncomingNode.run_complete formulas solver inventory
      beforeCaller before.core checkEmpty target incoming incomingScs memos initial
      realized storage root pending available closed bounded ranges
  obtain ⟨found, lookup, oldStored, _readSame⟩ :=
    (getValue_success r target before.core read (.unenumerated oldNode oldScs)).mp (by
      unfold Success
      rw [show ExceptT.run (getValue r target before.core) =
        [.ok (.unenumerated oldNode oldScs, read)] from
          by simpa only [Nat.add_zero] using reading 0]
      exact List.mem_singleton_self _)
  have foundTarget : found.representative = target := by
    obtain ⟨rootSize, rootPath⟩ := root
    exact (UnionFind.reaches_unique
      (UnionFind.findRoot_correct r before.core.representatives target found lookup).1 rootPath).1
  have readStored : read.values[target]? = some (.unenumerated oldNode oldScs) := by
    rw [frame.values, ← foundTarget]
    exact oldStored
  have readPaths : Roots read.representatives roots := by
    intro slot
    obtain ⟨size, path⟩ := paths slot
    exact ⟨size, (frame.reaches slot (roots slot) size).mpr path⟩
  have readCounts : EnumerationCanonicalWaiting.Correct roots read.values before.waiting := by
    simpa only [frame.values] using counts
  have readFlags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((read.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
    simpa only [frame.values] using flags
  have readAligned : read.counter = read.values.length := by
    simpa only [SupplyAligned, frame.counter, frame.values] using storage.aligned
  obtain ⟨k, written, cacheRun, _writtenCore, writtenFlags, writtenWaiting,
    _framedCore, _afterAligned, afterPaths, afterCounts, afterFlags⟩ :=
    SourcePruningEnumerationNativeIndex.gained_complete
      beforeCaller.checked.native.machine.heap afterCaller.checked.native.machine.heap
      post.effects.keeps (EnumerationExpandableIndex.frame read before) afterCore
      target oldNode oldScs incomingScs handle replacement roots readPaths readStored
      decoded readAligned readCounts readFlags writePrefix
  have afterCounter : afterCore.counter = before.core.counter := by
    simpa only [coreSame] using frame.counter
  have afterRepresentatives : afterCore.representatives = read.representatives := by
    rw [coreSame]
  refine ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final,
    next, replacement, handle, EnumerationExpandableIndex.frame afterCore written,
    reading, frame, runStable, writePrefix, coreSame, storedAfter, afterStorage,
    afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, ?_, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, writtenWaiting, afterFlags, writtenFlags, optional, present⟩
  intro extra
  rw [cacheRun extra]
  rfl

end MicroCFTA.SourcePruningEnumerationCachedIncoming
