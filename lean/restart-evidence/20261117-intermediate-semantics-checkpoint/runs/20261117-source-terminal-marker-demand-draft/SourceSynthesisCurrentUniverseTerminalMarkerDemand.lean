import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourcePruningEnumerationSharedChildObservedResources
import MicroCFTA.SourcePruningEnumerationSharedChildStableNeutral
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets
import MicroCFTA.SourcePruningEnumerationSharedIncomingBucketHistory

namespace MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerDemand
open Cache Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDependencies EnumerationCompleteness
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourcePruningEnumerationObservation
open SourcePruningEnumerationSharedSelectedContinuations
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {bits : Nat}
set_option autoImplicit false

/- Note [Source marker demand at a terminal raw class]
The accepted source fixes the original U marker and its complete native row.
The actual terminal dispatch supplies its raw winner and original target aliases.
The actual incoming singleton supplies the written native handle at that class.
Current resource facts identify the exact returned native readback.
Neutral semantics restricts every satisfying assignment at that same endpoint.
It does not supply an assignment or claim that a later marker was expanded.
The marker is a distinct demand. It is not a Type argument.
No source-wide nonterminal condition or worker budget changes here.
-/

private theorem nullary_meaning
    (entry : Interned NodeKey) (row : Edge) (leaf : row.children = [])
    (symbol : row.entry.key.symbol = literal "(->)")
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol)
    (accepted : InternedGuardedLanguage.meaning holds ambient (.node entry [row] 0 []) term) :
    term = .node (literal "(->)") [] := by
  rw [InternedGuardedLanguage.meaning] at accepted
  obtain ⟨⟨selected, member⟩, checked⟩ := accepted
  have same : selected = row := List.mem_singleton.mp member
  subst selected
  cases row with
  | mk edge children =>
      change children = [] at leaf
      subst children
      change edge.key.symbol = literal "(->)" at symbol
      rw [InternedGuardedLanguage.edgeMeaning] at checked
      obtain ⟨terms, head, forest, _guard⟩ := checked
      cases terms with
      | nil => simpa only [symbol] using head
      | cons first rest => cases forest

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem original_universe_terminal_marker_demand
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∃ (bodyEntry : Interned NodeKey) (marker : Node) (markerEntry : Interned NodeKey)
        (markerRow arrow : Edge) (rows : List Edge),
      body = .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] ∧
      marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
      markerRow.entry.key = ⟨literal "(->)", [], SourceSynthesisGeneralizeSyntax.top⟩ ∧
      arrow.children = [marker, .reference (.interned entry.identity), .reference (.interned entry.identity)] ∧
      arrow ∈ canonicalEdges (arrow :: rows) ∧
      ∀ (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
        (solver : SourceGuards.Entailment FullSyntax.Formula)
        (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached)
        (checkEmpty : Bool) (bucket : List Suspended) (roots : Nat → Nat) (memos : Memos),
        Grows sourceHeap caller.checked.native.machine.heap →
        Context formulas solver inventory caller memos →
        Safe before.core → Roots before.core.representatives roots →
        EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting →
        (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
          ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) →
        PendingRealized caller.checked.native.machine.heap before.core →
        (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
        Fits seed.2 caller.checked → Reserved bits seed (bucket.length + 1) →
        SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
        ∀ (held : Nat), held < before.core.counter → Avoids before.core.representatives held bucket →
        ∀ (r n p h k : Nat) (fragment : Fragment) (reached : Caller (bits + 2))
          (saved : Queries) (read returned : Core) (waiting : EnumerationWaitingIndex.Waiting) (after : Cached),
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true →
          ChildDispatch.run checkEmpty r n p h k bucket marker caller before memos.query =
            ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after) →
          ∃ (winner owner size handle : Nat) (storedBucket : List Suspended) (replacement : Node),
            after.core = returned ∧ fragment = .hole winner ∧
            UnionFind.Reaches returned.representatives winner owner size ∧
            returned.values[owner]? = some (.unenumerated (some handle) storedBucket) ∧
            SourcePruningEnumerationNodes.lookupNode reached.checked.native.machine.heap handle = some replacement ∧
            Available reached.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
            (∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
              UnionFind.SameClass returned.representatives winner sc.var) ∧
            ∀ (ambient : InternedGuardedLanguage.Env Symbol)
              (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient reached.checked.native.machine.heap) residualMeaning assignment returned →
                assignment winner = .node (literal "(->)") []
 := by
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, markerRead, arrowChildren, _arrowKey,
      _aligned, markerClosed, sourceAvailable, _kinds, retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  obtain ⟨markerEntry, markerRow, markerEq, markerChildren, markerKey⟩ := markerRead
  refine ⟨bodyEntry, marker, markerEntry, markerRow, arrow, rows,
    bodyEq, markerEq, markerChildren, markerKey, arrowChildren, retained, ?_⟩
  intro seed formulas solver inventory caller before checkEmpty bucket roots memos
    sourceGrowth initial safe paths counts flags realized bounded pending fits reserved known
    held heldBound heldAvoids r n p h k fragment reached saved read returned waiting after terminal observed
  have currentFacts : Facts caller.checked.native.machine.heap :=
    initial.ready.semantic.ready.semantic.1.normal.facts
  have markerStored : sourceHeap.nodeRecords markerEntry.key = some marker :=
    sourceAvailable.resident markerEntry (by rw [markerEq]; rfl)
  have available : Available caller.checked.native.machine.heap marker :=
    currentFacts.cached.nodes markerEntry.key marker
      (sourceGrowth.nodeRecords markerEntry.key marker markerStored)
  have coreSame : after.core = returned :=
    SourcePruningEnumerationChildDispatch.singleton_core checkEmpty r n p h k bucket marker
      caller reached before after memos.query saved fragment returned read waiting observed
  obtain ⟨final, next, afterRoots, resource⟩ :=
    ChildDispatch.observed_complete_with_fragments_resources seed formulas solver inventory caller before
      checkEmpty bucket marker roots memos initial safe paths counts flags realized bounded pending
      available markerClosed fits reserved known r n p h k [.ok (fragment, returned)] reached after
      saved read waiting observed (.inr ⟨fragment, returned, rfl⟩)
  obtain ⟨stable, _post, _querySame, _counter, _pathsAfter, _storageAfter, realizedAfter,
      _countsAfter, _flagsAfter, _origins, _protected, _references, _pendingReferences,
      _fragmentResources, _fitsAfter, _knownAfter⟩ := resource
  have ranges := ChildDispatch.initial_ranges seed formulas solver inventory caller before
    checkEmpty bucket marker roots memos initial safe paths counts bounded pending realized available
    markerClosed fits reserved known
  have semantic := ChildDispatch.stable_neutral_semantics formulas solver inventory caller before
    checkEmpty bucket marker roots memos initial safe paths counts flags realized bounded pending
    available markerClosed ranges stable held heldBound heldAvoids
  obtain ⟨first, rest, descendants, recorded, winner, joined, foldCaller, foldQueries, folded, foldOuter,
      _partitioned, _prefix, _foldedCall, _foldEndpoint, incomingCall, _recordedSame,
      _joinedValues, hole, _foldForest, _readForest, aliases⟩ :=
    ChildDispatch.terminal_singleton_final_raw_target_incidence checkEmpty r n p h k bucket marker
      caller before memos.query terminal fragment reached saved read returned waiting (some after) roots paths observed
  obtain ⟨found, oldNode, oldScs, handle, lookup, _oldStored, readSame, written, installed, _ancestry⟩ :=
    SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history checkEmpty r n p h
      foldCaller folded winner marker descendants foldQueries returned reached saved read incomingCall
  have rootPath := UnionFind.findRoot_correct r folded.representatives winner found lookup
  have actualPath : UnionFind.Reaches returned.representatives winner found.representative found.size := by
    simpa only [written, readSame] using rootPath.2 rootPath.1
  have returnedRealized : PendingRealized reached.checked.native.machine.heap returned := by
    rw [← coreSame]
    exact realizedAfter
  obtain ⟨replacement, decoded, replacementAvailable, replacementClosed⟩ :=
    returnedRealized found.representative handle (descendants ++ oldScs) installed
  refine ⟨winner, found.representative, found.size, handle, descendants ++ oldScs, replacement,
    coreSame, hole, actualPath, installed, decoded, replacementAvailable, replacementClosed, aliases, ?_⟩
  intro ambient residualMeaning assignment satisfied
  have neutral := EnumerationFrame.neutralize_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient reached.checked.native.machine.heap) residualMeaning assignment held returned satisfied
  have restrictions := (semantic ambient residualMeaning assignment fragment returned
    (List.mem_singleton_self _)).mp neutral
  have markerAccepted := restrictions.2.1
  rw [hole, fill, markerEq] at markerAccepted
  exact nullary_meaning markerEntry markerRow markerChildren (congrArg EdgeKey.symbol markerKey)
    (SourceEqualityPCSGuard.holds formulas solver) ambient (assignment winner) markerAccepted

end MicroCFTA.SourceSynthesisCurrentUniverseTerminalMarkerDemand
