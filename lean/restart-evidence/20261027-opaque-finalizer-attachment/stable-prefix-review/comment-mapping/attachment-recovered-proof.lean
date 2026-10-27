import MicroCFTA.SourcePruningEnumerationOpaqueStablePrefixResources
import MicroCFTA.SourcePruningEnumerationOwnPrefixPacket
import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

namespace MicroCFTA.SourcePruningEnumerationOpaqueEvent
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeHookResources (CompletedHeadReceipt)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "cost" => SourcePruningEnumerationTraversalCompletion.cost
variable {Typing : Type} {bits : Nat}

/-- An opaque boundary preparation ignores the unused native-index fuel. -/
theorem opaque_prepare_fuel
    (heap : InternedConstructorTemplates.State Symbol Constraint) (firstFuel nextFuel : Nat)
    (bucket : List Suspended) (value : Node) (before : Cached)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    SourcePruningEnumerationCachedPrepare.prepareChild heap firstFuel bucket value before =
      SourcePruningEnumerationCachedPrepare.prepareChild heap nextFuel bucket value before := by
  cases value with
  | empty => simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | reference name => simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | node entry edges depth free =>
      simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | union entry members depth free | mu entry members depth free => rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual stable completed head retains its opaque child at the same final cache. -/
theorem completed_head_opaque_isolated
    (seed : Seed) (inherited : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (bound : Nat) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (headCache : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved headCache returnedInventory returnedMemos)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (consumed suffix : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
    (location : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries =
      consumed ++ (value, bucket) :: suffix)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ held handle, lookupNode reached.checked.native.machine.heap handle = some value ∧
      EnumerationDischargeHistory.IsolatedPending held handle headCache.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := head.admission.packet.valid
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨parent, parentLookup, parentAvailable, parentClosed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry edges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    head.admission.ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core head.admission.packet.pending
    uv (some handle) scs stored
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots head.admission.packet.context.ready.semantic.ready parentAvailable parentClosed selected
      before head.admission.packet.safe realized paths counts flags bounded pending head.allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged := inputs.map (fun input => (input.1, input.2,
    SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
  have stagedInputs : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    simp only [staged, List.map_map]
    exact List.map_id _
  have ownPacket := own_prefix_packet formulas solver inventory caller memos metadata before own tries.length
    head.admission.packet ownCore ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩
  have originalReserved : Reserved bits seed (cost inputs) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, head.allowed, ↓reduceIte,
      projected, SourcePruningEnumerationSelectedEdge.cost, inputs] using head.admission.reserved
  obtain ⟨r, n, p, h, k, _fragments, _afterCaller, _after, _savedQueries, _final, _next, _afterRoots,
    _result, _running, _post, _querySame, _growth, _pathsAfter, _storageAfter, _realizedAfter,
    _countsAfter, _flagsAfter, _origin, _expandedProtected, _rootsProtected, _references,
    _pendingHistory, _fragmentBounds, _shape, _returnedFits, _returnedKnown,
    eventAdmission, prefixResult, prefixRunning⟩ :=
    complete_with_stable_prefix_resources seed formulas solver inventory caller own checkEmpty inputs roots memos
      head.admission.packet.context ownSafe ownPaths ownCounts ownFlags ownRealized genuine
      head.admission.bounded originalReserved head.admission.known consumed ((value, bucket) :: suffix) location
  let B := r + n + p + h + k
  let W := B + bound
  have currentHead : SourcePruningEnumerationCapturedEdge.run checkEmpty W W W W W uv scs edge
      caller before memos.query = some (.complete fragment reached saved headCache) := by
    simpa only [W, Nat.add_comm] using head.running B
  obtain ⟨prefixFragments, _suffixFragments, eventCaller, eventBefore, opaqueAfter, _childCache,
    eventQueries, _oldHandle, _fragmentShape, prefixTrace, _childObservation, opaqueRow,
    _encoded, _allocated, _suffixTrace, _finalized⟩ :=
    captured_opaque_event checkEmpty W W W W W uv scs edge caller reached before own headCache
      memos.query saved edge.entry.key.symbol staged residual fragment consumed suffix value bucket ownRun
      (stagedInputs.trans location) boundary nonterminal currentHead
  have prefixFixed : prefixResult = .complete prefixFragments eventCaller eventQueries eventBefore := by
    have canonical := prefixRunning bound
    have actual := SourcePruningEnumerationChildTraversal.trace_complete prefixTrace
    exact canonical.symm.trans actual
  obtain ⟨eventInventory, eventMemos, _eventPost, eventQuery, eventPacket, eventGrowth,
    remainingGenuine, eventFits, eventKnown, eventReserved⟩ :=
    eventAdmission metadata ownPacket bound prefixFragments eventCaller eventBefore eventQueries prefixTrace
  obtain ⟨available, closed, _eventBounded, _eventPending⟩ :=
    remainingGenuine value bucket (by simp)
  have suffixGenuine : ∀ incoming retained, (incoming, retained) ∈ suffix →
      Available eventCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ retained, sc.var < eventBefore.core.counter) ∧ InputsPending eventBefore.core retained := by
    intro incoming retained member
    exact remainingGenuine incoming retained (List.mem_cons_of_mem _ member)
  have suffixReserved : Reserved bits (advance seed (cost consumed)) (cost suffix) :=
    eventReserved.prefix (by change cost suffix ≤ bucket.length + 1 + cost suffix; omega)
  obtain ⟨opaqueHandle, sr, sn, sp, sh, sk, suffixResultFragments, suffixCaller, suffixCache,
    suffixQueries, _suffixMemos, _suffixInventory, _suffixRoots, suffixResult,
    _encoded, lookup, _opaqueCore, suffixFull, _suffixIsolated, finalizerIsolated⟩ :=
    EnumerationDischargeHistory.opaque_suffix_complete_isolated_resources
      (advance seed (cost consumed)) formulas solver eventInventory eventCaller eventMemos metadata
      eventBefore opaqueAfter value bucket W eventPacket available closed boundary nonterminal opaqueRow
      checkEmpty suffix suffixGenuine eventFits suffixReserved eventKnown
  obtain ⟨suffixRunning, suffixPost, _suffixQuery, _suffixGrowth, _suffixPaths, _suffixStorage,
    _suffixRealized, _suffixCounts, _suffixFlags, _suffixOrigin, _suffixExpandedProtected,
    _suffixRootsProtected, _suffixReferences, _suffixPending, _suffixBounds, suffixShape,
    _suffixFits, _suffixKnown⟩ := suffixFull
  let padding := sr + sn + sp + sh + sk
  let nextWork := B + bound + padding
  have nextHead : SourcePruningEnumerationCapturedEdge.run checkEmpty nextWork nextWork nextWork nextWork
      nextWork uv scs edge caller before memos.query = some (.complete fragment reached saved headCache) := by
    simpa only [nextWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using head.running (B + padding)
  obtain ⟨nextPrefixFragments, nextSuffixFragments, nextEventCaller, nextEventBefore, nextOpaqueAfter,
    nextChildCache, nextEventQueries, _nextHandle, _nextFragmentShape, nextPrefixTrace,
    _nextObservation, nextOpaqueRow, _nextEncoded, _nextAllocated, nextSuffixTrace, nextFinalized⟩ :=
    captured_opaque_event checkEmpty nextWork nextWork nextWork nextWork nextWork uv scs edge caller reached
      before own headCache memos.query saved edge.entry.key.symbol staged residual fragment consumed suffix
      value bucket ownRun (stagedInputs.trans location) boundary nonterminal nextHead
  have nextPrefixFixed : prefixResult =
      .complete nextPrefixFragments nextEventCaller nextEventQueries nextEventBefore := by
    have canonical : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
        nextWork nextWork consumed caller own memos.query = prefixResult := by
      simpa only [nextWork, B, Nat.add_assoc] using prefixRunning (bound + padding)
    have actual := SourcePruningEnumerationChildTraversal.trace_complete nextPrefixTrace
    exact canonical.symm.trans actual
  have prefixSame := SourcePruningEnumerationChildTraversal.Result.complete.inj
    (prefixFixed.symm.trans nextPrefixFixed)
  obtain ⟨fragmentsSame, callerSame, queriesSame, cacheSame⟩ := prefixSame
  subst nextPrefixFragments nextEventCaller nextEventQueries nextEventBefore
  have sameOpaque : opaqueAfter = nextOpaqueAfter := by
    have canonical := (opaque_prepare_fuel eventCaller.checked.native.machine.heap W nextWork bucket value
      eventBefore boundary).symm.trans opaqueRow
    exact (Prod.mk.inj (List.cons.inj (Option.some.inj (canonical.symm.trans nextOpaqueRow))).1).2
  subst nextOpaqueAfter
  have sufficient : sr ≤ nextWork ∧ sn ≤ nextWork ∧ sp ≤ nextWork ∧ sh ≤ nextWork ∧ sk ≤ nextWork := by
    dsimp only [nextWork, padding]
    omega
  have actualSuffix : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
      nextWork nextWork suffix eventCaller opaqueAfter eventMemos.query =
      .complete nextSuffixFragments reached saved nextChildCache := by
    simpa only [eventQuery] using SourcePruningEnumerationChildTraversal.trace_complete nextSuffixTrace
  have canonicalSuffix : SourcePruningEnumerationChildTraversal.run checkEmpty nextWork nextWork nextWork
      nextWork nextWork suffix eventCaller opaqueAfter eventMemos.query = suffixResult := by
    have canonical := suffixRunning (nextWork - sr) (nextWork - sn) nextWork nextWork (nextWork - sk)
      (by omega) (by omega)
    have rSame : sr + (nextWork - sr) = nextWork := by omega
    have nSame : sn + (nextWork - sn) = nextWork := by omega
    have kSame : sk + (nextWork - sk) = nextWork := by omega
    simpa only [rSame, nSame, kSame] using canonical
  have suffixSame := canonicalSuffix.symm.trans actualSuffix
  rcases suffixShape with ⟨suffixComplete, _suffixSafe, _suffixHistory⟩ | ⟨outer, waiting, suffixStopped⟩
  · rw [suffixComplete] at suffixSame
    have endpoints := SourcePruningEnumerationChildTraversal.Result.complete.inj suffixSame
    obtain ⟨fragmentsSame, callerSame, queriesSame, cacheSame⟩ := endpoints
    subst nextSuffixFragments suffixCaller suffixQueries nextChildCache
    have different : uv ≠ eventBefore.core.counter := by
      have inside := head.admission.ready.inside
      omega
    refine ⟨eventBefore.core.counter, opaqueHandle, ?_, ?_⟩
    · exact lookupNode_keeps eventCaller.checked.native.machine.heap reached.checked.native.machine.heap
        suffixPost.effects.keeps opaqueHandle value lookup
    · exact finalizerIsolated residual fragment nextWork uv headCache different nextFinalized
  · rw [suffixStopped] at suffixSame
    cases suffixSame

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
