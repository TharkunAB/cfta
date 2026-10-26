import MicroCFTA.SourcePruningEnumerationCachedIncoming
import MicroCFTA.SourcePruningEnumerationIncomingNodeResources

/-!
# Initial resources for the cached incoming action

The existing producer supplies every cache and language receipt.
Its same actual observation supplies the final resource and guard bounds.
The input profile and alphabet determine both bounds before execution.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedIncoming
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Initial bounds construct the full cached incoming packet and its final resources. -/
theorem complete_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
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
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read : EnumerationState.State Symbol Constraint) (afterCaller : Caller (bits + 2))
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
        ∃ (old query : Node) (queried : Checked (bits + 2)),
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
      Fits (SourcePruningEnumerationIncomingQuery.forecast alphabet profile) afterCaller.checked ∧
      Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
        afterCaller.checked.native.machine.heap := by
  have ranges := SourcePruningEnumerationIncomingNode.initial_ranges profile beforeCaller before.core
    target incoming initial.ready realized available closed fits room
  obtain ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present⟩ :=
    complete formulas solver inventory beforeCaller before checkEmpty target incoming incomingScs memos roots
      initial storage realized paths counts flags root pending available closed bounded ranges
  have observed := originalRun 0 0 p h (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  have resources := SourcePruningEnumerationIncomingNode.observed_resources alphabet profile formulas solver
    inventory beforeCaller before.core checkEmpty r n p h target incoming incomingScs memos
      initial realized available closed fits room known observed
  exact ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present,
    resources.1, resources.2⟩

end MicroCFTA.SourcePruningEnumerationCachedIncoming
