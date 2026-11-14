import MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot
import MicroCFTA.SourceSynthesisCurrentSharedGoalSingletonPrefix
import MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFirstWrite
import MicroCFTA.SourcePruningEnumerationSharedChildRawTargets

/-!
# Source provenance from the actual first shared filter child

The accepted source build identifies the first prepared goal input.
Its own fresh class supplies the unbound slot before the actual prefix.
The singleton prefix and same-root shared fold retain the entry caller.
The actual incoming assignment then stores the original source goal.
The caller context is derived at the returned endpoint.
The source entry and complete visitor reach remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedRootGoalFirstChild
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open EnumerationCorrectness (StorageValid)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open InternedBoundaryAtoms (atoms)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Input" => Node × List Suspended ×
  Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The actual first shared child stores the same source goal and retains its entry caller context. -/
theorem source_root_goal_first_child
    {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue inventory.source)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : inventory.source.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRow : EdgeValue Symbol Constraint)
    (rootMember : rootRow ∈ InternedEdgeResidency.nodeEdges rootValue)
    (caller : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (captured middle : Cached) (storage : StorageValid captured.core)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap [] rootRow captured =
        some [((symbol, staged, residual), middle)])
    (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol)))
    (selected : staged[0]? = some (incoming, bucket, action))
    (checkEmpty : Bool) (r n p h k : Nat) (queries : Queries)
    (fragment : Fragments.Fragment Symbol) (after : Core)
    (afterCaller : Caller width) (savedQueries : Queries) (read : Core)
    (moved : EnumerationWaitingIndex.Waiting) (afterCache : Option Cached)
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming caller middle queries =
        ((.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved), afterCache)) :
    ∃ (goalHeap : InternedConstructorTemplates.State Symbol Constraint) (handle : Nat)
        (joined : Core) (found : UnionFind.Result),
      build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
        .done incoming goalHeap ∧
      bucket = [⟨.terminal, captured.core.counter⟩] ∧
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r
        ⟨.terminal, captured.core.counter⟩ [] middle.waiting middle.core) =
          [.ok (([captured.core.counter], captured.core.counter, middle.waiting), joined)] ∧
      SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty n p h
        [captured.core.counter] caller joined captured.core.counter queries =
          (.ok (some [.ok ((), joined)]), caller, queries, joined) ∧
      SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
        caller joined captured.core.counter incoming [] queries =
          (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) ∧
      UnionFind.findRoot r joined.representatives captured.core.counter = some found ∧
      found.representative = captured.core.counter ∧
      joined.values[found.representative]? = some (.unenumerated none []) ∧
      afterCaller = caller ∧ savedQueries = queries ∧
      Context formulas solver inventory afterCaller memos ∧
      Available inventory.source incoming ∧
      Available afterCaller.checked.native.machine.heap incoming ∧
      incoming.free = [] ∧ Annotated (Origin (encodedLibrary lib)) incoming ∧
      (∀ atom ∈ atoms incoming, atom = .mu entry.identity) ∧
      encodeNode incoming = some handle ∧
      lookupNode afterCaller.checked.native.machine.heap handle = some incoming ∧
      fragment = .hole captured.core.counter ∧ read = joined ∧
      after.values[captured.core.counter]? = some (.unenumerated (some handle) []) := by
  obtain ⟨goal, _freshGoalHeap, goalAction, _freshGoalBuild, freshSelected,
      _freshPartition, middleShape, _middleWaiting, _middleExpandable,
      freshSlot, missing, _firstRead⟩ :=
    SourceSynthesisCurrentSharedSourceGoalFreshSlot.source_goal_prepared_fresh_slot
      inventory lib query signed whole accepted rootValue built rootRow rootMember
      caller captured middle storage symbol staged residual prepared
  let uv := captured.core.counter
  let terminal : Suspended := ⟨.terminal, uv⟩
  have inputSame : (incoming, bucket, action) = (goal, [terminal], goalAction) :=
    Option.some.inj (selected.symm.trans freshSelected)
  have bucketSame : bucket = [terminal] :=
    congrArg (fun input : Input => input.2.1) inputSame
  have terminalAny : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
    rw [bucketSame]
    rfl
  have total : UnionFind.Total middle.core.representatives := by
    rw [middleShape]
    exact storage.total
  obtain ⟨roots, paths⟩ := EnumerationSchedule.roots_exist middle.core.representatives total
  obtain ⟨first, rest, descendants, recorded, winner, joined,
      foldCaller, foldQueries, folded, foldOuter, partitioned, prefixObserved,
      foldObserved, foldedOuter, incomingObserved, _recordedMap, _joinedValues,
      fragmentShape, _rawAliases⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_raw_target_incidence
      checkEmpty r n p h k bucket incoming caller middle queries terminalAny
      fragment afterCaller savedQueries read after moved afterCache roots paths actual
  have partitionExact : ([terminal] : List Suspended).partition
      (fun sc => EqualityTrie.isTerminal sc.trie) = ([terminal], []) := rfl
  have partitionSame : ([terminal], []) = (first :: rest, descendants) := by
    rw [bucketSame, partitionExact] at partitioned
    exact partitioned
  have firstRestSame := List.cons.inj (Prod.mk.inj partitionSame).1
  have firstSame : first = terminal := firstRestSame.1.symm
  have restSame : rest = [] := firstRestSame.2.symm
  have descendantsSame : descendants = [] := (Prod.mk.inj partitionSame).2.symm
  have prefixActual : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      r terminal [] middle.waiting middle.core) = [.ok ((recorded, winner, moved), joined)] := by
    simpa only [firstSame, restSame] using prefixObserved
  obtain ⟨found, recordedSame, winnerSame, movedSame, _joinedShape,
      foldExact, lookup, foundRoot, foundForest, oldNone, prefixContext⟩ :=
    SourceSynthesisCurrentSharedGoalSingletonPrefix.singleton_goal_prefix_shared_fold
      formulas solver inventory caller memos initial checkEmpty r n p h uv
      middle.core joined middle.waiting moved recorded winner queries missing freshSlot prefixActual
  have foldTupleSame := foldExact.symm.trans foldObserved
  have foldCallerSame : foldCaller = caller :=
    (congrArg (fun result => result.2.1) foldTupleSame).symm
  have foldQueriesSame : foldQueries = queries :=
    (congrArg (fun result => result.2.2.1) foldTupleSame).symm
  have foldOuterSame : foldOuter = joined :=
    (congrArg (fun result => result.2.2.2) foldTupleSame).symm
  have foldedSame : folded = joined := foldedOuter.trans foldOuterSame
  have incomingActual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
      caller joined uv incoming [] queries =
      (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) := by
    simpa only [foldCallerSame, foldedSame, winnerSame, descendantsSame, foldQueriesSame]
      using incomingObserved
  have reading : UnionFind.findRoot r joined.representatives uv = some found := by
    simpa only [winnerSame] using lookup
  have noDescendants : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 = [] := by
    rw [bucketSame]
    rfl
  have incomingPartitioned : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
      caller joined uv incoming (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 queries =
      (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read) := by
    rw [noDescendants]
    exact incomingActual
  obtain ⟨goalHeap, handle, goalBuilt, sourceAvailable, available, closed, annotated, onlyU,
      encoded, decoded, callerSame, queriesSame, readSame, _writtenShape, writtenSlot⟩ :=
    SourceSynthesisCurrentSharedSourceGoalFirstWrite.source_goal_first_assignment
      formulas solver inventory lib query signed whole accepted rootValue built
      key entry body depth ordinary stored rootRow rootMember caller memos prefixContext
      [] captured middle symbol staged residual prepared incoming bucket action selected
      checkEmpty r n p h uv joined queries found [] reading oldNone
      after afterCaller savedQueries read incomingPartitioned
  have returnedContext : Context formulas solver inventory afterCaller memos := by
    rw [callerSame]
    exact prefixContext
  have readJoined : read = joined := by
    rw [foundForest] at readSame
    exact readSame
  have fragmentFresh : fragment = .hole uv := by
    rw [fragmentShape, winnerSame]
  have storedGoal : after.values[uv]? = some (.unenumerated (some handle) []) := by
    rw [foundRoot, noDescendants] at writtenSlot
    exact writtenSlot
  have literalPrefix : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      r terminal [] middle.waiting middle.core) = [.ok (([uv], uv, middle.waiting), joined)] := by
    simpa only [recordedSame, winnerSame, movedSame] using prefixActual
  have literalFold : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty n p h [uv] caller joined uv queries =
      (.ok (some [.ok ((), joined)]), caller, queries, joined) := by
    simpa only [recordedSame, winnerSame] using foldExact
  exact ⟨goalHeap, handle, joined, found, goalBuilt, bucketSame, literalPrefix, literalFold,
    incomingActual, reading, foundRoot, oldNone, callerSame, queriesSame, returnedContext,
    sourceAvailable, available, closed, annotated, onlyU, encoded, decoded,
    fragmentFresh, readJoined, storedGoal⟩

end MicroCFTA.SourceSynthesisCurrentSharedRootGoalFirstChild
