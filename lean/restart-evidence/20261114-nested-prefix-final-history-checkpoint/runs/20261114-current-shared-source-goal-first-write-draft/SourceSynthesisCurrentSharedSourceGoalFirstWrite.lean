import MicroCFTA.SourceSynthesisCurrentInitialFilterInterval
import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceSynthesisCurrentSharedIncomingNativeObservation
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourceSynthesisOwnChildTerminals

/-!
# Source provenance at a shared first assignment

The actual prepared filter input at position zero retains its source goal.
An observed shared first assignment stores that exact input.
The source build and the entry context supply its value certificates.
The incoming suspended variables retain the literal partition projection.
This result does not identify later descendant values with the source goal.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFirstWrite
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts (Facts empty_facts)
open InternedNestedConstruction (Outcome)
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
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

set_option autoImplicit false

/-- An actual first assignment of the prepared goal retains its original source certificates. -/
theorem source_goal_first_assignment
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
    (scs : List Suspended) (captured middle : Cached)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs rootRow captured =
        some [((symbol, staged, residual), middle)])
    (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol)))
    (selected : staged[0]? = some (incoming, bucket, action))
    (checkEmpty : Bool) (representativeFuel nativeFuel p h target : Nat)
    (before : Core) (queries : Queries) (found : UnionFind.Result)
    (oldScs : List Suspended)
    (reading : UnionFind.findRoot representativeFuel before.representatives target = some found)
    (slot : before.values[found.representative]? = some (.unenumerated none oldScs))
    (after : Core) (afterCaller : Caller width) (savedQueries : Queries) (read : Core)
    (actual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel
      nativeFuel p h caller before target incoming
      (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 queries =
        (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read)) :
    ∃ (goalHeap : State Symbol Constraint) (handle : Nat),
      build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
        .done incoming goalHeap ∧
      Available inventory.source incoming ∧
      Available afterCaller.checked.native.machine.heap incoming ∧
      incoming.free = [] ∧ Annotated (Origin (encodedLibrary lib)) incoming ∧
      (∀ atom ∈ atoms incoming, atom = .mu entry.identity) ∧
      encodeNode incoming = some handle ∧
      lookupNode afterCaller.checked.native.machine.heap handle = some incoming ∧
      afterCaller = caller ∧ savedQueries = queries ∧
      read = {before with representatives := found.forest} ∧
      after = {read with
        values := read.values.set found.representative
          (.unenumerated (some handle)
            ((bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 ++ oldScs))
        recursionAncestry := fun other => if other = found.representative then
          (read.expansionAncestry ++ read.recursionAncestry found.representative).eraseDups
          else read.recursionAncestry other} ∧
      after.values[found.representative]? = some (.unenumerated (some handle)
        ((bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 ++ oldScs)) := by
  obtain ⟨_chunks, goal, _candidate, goalHeap, _candidateAfter, _edgeAfter,
      _chunksRun, _wholeShape, _symbol, constraint, children, goalBuilt,
      _candidateContext, _candidateBuilt, _edgeMade, _rootMade, _candidateGrowth, _factory⟩ :=
    SourceSynthesisCurrentFirstFilterSourceLink.current_initial_filter_interval
      lib query signed whole accepted rootValue inventory.source built rootRow rootMember
  have projected : SourcePruningEnumerationConstraint.project rootRow.entry.key.constraint =
      some (EnumerationEquality.readClasses [[[0], [1, 0]]], none) := by
    rw [constraint]
    exact SourceSynthesisOwnChildTerminals.filter_projection
  have inputShape := SourcePruningEnumerationCachedOwn.prepare_inputs
    caller.checked.native.machine.heap scs rootRow captured middle
    (EnumerationEquality.readClasses [[[0], [1, 0]]]) none
    (symbol, staged, residual) projected prepared
  have mappedShape := congrArg (fun result : Symbol × List Input × Option Constraint =>
    result.2.1.map (fun input => input.1)) inputShape
  have childValues : staged.map (fun input => input.1) = rootRow.children := by
    simpa only [SourcePruningEnumerationEdgeInputs.children, List.map_map,
      Function.comp_def, List.zipIdx_map_fst] using mappedShape
  have selectedValue : (staged.map (fun input => input.1))[0]? = some incoming := by
    simp only [List.getElem?_map, selected, Option.map_some]
  rw [childValues, children] at selectedValue
  have incomingSame : incoming = goal := (Option.some.inj selectedValue).symm
  have checked := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)
  have sourceFacts : Facts inventory.source := inventory.facts
  have rootAvailable := checked.result rootValue inventory.source built
  have rowResident := InternedEdgeResidency.resident_edges inventory.source sourceFacts.linked
    rootValue rootAvailable.resident rootRow rootMember
  have goalAvailable : Available inventory.source goal :=
    sourceFacts.cached.edges rootRow.entry.key rootRow rowResident goal
      (by rw [children]; exact List.mem_cons_self)
  have goalClosed := InternedFreshOrdinarySourceFreeNames.closed_free_empty
    (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) goal goalHeap goalBuilt
  have allowed : SourceEqualityAnnotationConstruction.Allowed (Origin (encodedLibrary lib))
      (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) := by
    simpa only [SourceSynthesisCurrentContext.typeNode,
      SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      SourceSynthesisOriginalTypeAnnotations.rigid_allowed literal (encodedLibrary lib)
        (SourceSynthesisPr210TypeReflection.encodeTy query.queryGoal)
  have annotatedBuild := SourceCurrentHereditaryConstruction.build (Origin (encodedLibrary lib))
    (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty empty_facts
    (by intro value member; cases member) allowed (by intro value member; cases member)
    (SourceCurrentHereditaryConstruction.MuStored.empty (Origin (encodedLibrary lib)))
  have goalAnnotated := annotatedBuild.result goal goalHeap goalBuilt
  have goalAtoms := SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue inventory.source built key entry body depth ordinary stored
    goal goalAvailable goalClosed
  have available : Available inventory.source incoming := by rw [incomingSame]; exact goalAvailable
  have closed : incoming.free = [] := by rw [incomingSame]; exact goalClosed
  have annotated : Annotated (Origin (encodedLibrary lib)) incoming := by
    rw [incomingSame]; exact goalAnnotated
  have onlyU : ∀ atom ∈ atoms incoming, atom = .mu entry.identity := by
    rw [incomingSame]; exact goalAtoms
  have currentAvailable : Available caller.checked.native.machine.heap incoming :=
    Available.grows inventory.source caller.checked.native.machine.heap
      initial.admitted.growth initial.admitted.history available
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    caller.checked.native.machine.heap incoming
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent currentAvailable closed
  let descendants := (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2
  let readCore : Core := {before with representatives := found.forest}
  let written : Core := {readCore with
    values := readCore.values.set found.representative
      (.unenumerated (some handle) (descendants ++ oldScs))
    recursionAncestry := fun other => if other = found.representative then
      (readCore.expansionAncestry ++ readCore.recursionAncestry found.representative).eraseDups
      else readCore.recursionAncestry other}
  have raw : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      found.representative handle descendants oldScs incoming readCore) =
      (if incoming = .empty then [] else [.ok ((), written)]) := by
    cases incoming with
    | empty => simp only [↓reduceIte]; rfl
    | reference name => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | node nodeEntry edges nodeDepth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | union unionEntry members unionDepth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | mu muEntry muBody muDepth muOrdinary => simp only [reduceCtorEq, ↓reduceIte]; rfl
  have exactOperation : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel
      nativeFuel p h caller before target incoming descendants queries =
      (.ok (some (if incoming = .empty then [] else [.ok ((), written)])), caller, queries, readCore) := by
    simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, encoded, raw]
  have normalized := exactOperation.symm.trans actual
  have callerSame : afterCaller = caller :=
    (congrArg (fun result => result.2.1) normalized).symm
  have queriesSame : savedQueries = queries :=
    (congrArg (fun result => result.2.2.1) normalized).symm
  have readSame : read = readCore :=
    (congrArg (fun result => result.2.2.2) normalized).symm
  have outcomeSame : (if incoming = .empty then [] else [.ok ((), written)]) = [.ok ((), after)] :=
    Option.some.inj (Except.ok.inj (congrArg (fun result => result.1) normalized))
  have singletonSame : ([Except.ok ((), written)] : List (Except EnumerationState.Error (Unit × Core))) =
      [Except.ok ((), after)] := by
    by_cases absent : incoming = .empty
    · simp only [absent, ↓reduceIte] at outcomeSame
      cases outcomeSame
    · simpa only [absent, ↓reduceIte] using outcomeSame
  have writtenSame : after = written :=
    (Prod.mk.inj (Except.ok.inj (List.cons.inj singletonSame).1)).2.symm
  have inside : found.representative < readCore.values.length :=
    (List.getElem?_eq_some_iff.mp slot).1
  have writtenSlot : written.values[found.representative]? =
      some (.unenumerated (some handle) (descendants ++ oldScs)) :=
    List.getElem?_set_self inside
  refine ⟨goalHeap, handle, ?_, available, ?_, closed, annotated, onlyU, encoded,
    ?_, callerSame, queriesSame, readSame, ?_, ?_⟩
  · rw [incomingSame]
    exact goalBuilt
  · rw [callerSame]
    exact currentAvailable
  · rw [callerSame]
    exact decoded
  · rw [readSame]
    exact writtenSame
  · rw [writtenSame]
    exact writtenSlot

end MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFirstWrite
