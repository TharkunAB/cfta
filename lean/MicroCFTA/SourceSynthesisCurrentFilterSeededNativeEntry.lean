import MicroCFTA.SourceSynthesisCurrentInitialFilterInterval
import MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowFacts
import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceCurrentAllocatedSeededQuery

/-!
# The native entry of a completed source filter query

The source narrowing retains original filter rows and constructor history.
A completed seeded graph projects the candidate before the rigid goal seed.
The seed projection changes no heap or native table.
Its actual first node instruction uses the ordinary native step.
Later allocated edge instructions still need their own correspondence proof.
This result does not prove that the root visitor reaches the seeded graph.
-/
namespace MicroCFTA.SourceSynthesisCurrentFilterSeededNativeEntry
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedNestedProvenance (Edges)
open InternedBinderProtocol (NodeKey)
open InternedBoundaryAtoms
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentAllocatedSeededQuery (Seeded Fold Operand)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionCode (requestNode)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "filterGuard" => SourceSynthesisGeneralizeSyntax.eqGuard [[[0], [1, 0]]]

set_option autoImplicit false

private theorem current_root_ordinary
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap) :
    SourceEqualityRequiredCache.Ordinary rootValue := by
  obtain ⟨_chunks, _chunksRun, wholeShape, _factory⟩ :=
    SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands
      lib query signed whole accepted
  have rootSyntax : ∃ rows : List (EdgeSyntax Symbol Guard),
      ordinarySymbols whole = .node rows := by
    rw [wholeShape]
    exact ⟨_, rfl⟩
  obtain ⟨sourceRows, sourceShape⟩ := rootSyntax
  have nodeBuilt := built
  rw [sourceShape, build] at nodeBuilt
  have checked := InternedFreshOrdinaryFacts.buildEdges_verified sourceRows []
    (empty : State Symbol Guard) empty_facts (by intro value member; cases member)
  cases rowsDone : buildEdges sourceRows [] (empty : State Symbol Guard) with
  | pending key state =>
      simp only [rowsDone, Outcome.bind] at nodeBuilt
      cases nodeBuilt
  | done rows middle =>
      have same : (run (makeNode rows) middle).1 = rootValue ∧
          (run (makeNode rows) middle).2 = heap := by
        apply Outcome.done.inj
        simpa only [rowsDone, Outcome.bind, work] using nodeBuilt
      have middleFacts : Facts middle := by
        simpa only [rowsDone, Outcome.state] using checked.facts
      rw [← same.1]
      exact SourceEqualityRequiredCache.node_ordinary rows middle middleFacts
        (checked.result rows middle rowsDone)

/-- The actual initial narrowing retains the source records and issued references. -/
theorem current_initial_narrowing_history
    {Typing Key : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (fuel : Nat)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (observed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      fuel 0 rootValue heap = .done result after) :
    Grows heap after ∧ Extends heap.nodes.issued after.nodes.issued := by
  have ordinary := current_root_ordinary lib query signed whole accepted rootValue heap built
  have checked := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)
  have facts : Facts heap := by simpa only [built, Outcome.state] using checked.facts
  have available : Available heap rootValue := checked.result rootValue heap built
  by_cases inside : 0 ∈ metadata.types
  · rw [SourcePruningOuterNarrow.narrow_type
      holeKey fits admits metadata fuel 0 rootValue heap inside] at observed
    obtain ⟨rfl, rfl⟩ := MergedSourceComparison.Result.done.inj observed
    exact ⟨grows_refl _, extends_refl _⟩
  · have notMu : ∀ entry body depth ordinaryShape,
        rootValue ≠ .mu entry body depth ordinaryShape := by
      intro entry body depth ordinaryShape same
      rw [same] at ordinary
      cases ordinary
    rw [SourcePruningOuterNarrow.narrow_fallback
      holeKey fits admits metadata fuel 0 rootValue heap notMu inside] at observed
    have exposed : MergedFreshOrdinaryExposure.nodeEdges fuel rootValue heap =
        .done (InternedEdgeResidency.nodeEdges rootValue) heap := by
      cases rootValue with
      | empty | node => rfl
      | reference | union | mu => cases ordinary
    rw [SourcePruningNativeView.narrowAt, exposed] at observed
    let selected := (InternedEdgeResidency.nodeEdges rootValue).filter
      (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing 0))
    have same : (run (makeNode selected) heap).1 = result ∧
        (run (makeNode selected) heap).2 = after :=
      MergedSourceComparison.Result.done.inj observed
    have originalResident : Edges heap (InternedEdgeResidency.nodeEdges rootValue) :=
      InternedEdgeResidency.resident_edges heap facts.linked rootValue available.resident
    have selectedResident : Edges heap selected := by
      intro row member
      exact originalResident row (List.mem_filter.mp member).1
    have reconstructed := node_verified selected heap facts selectedResident
    rw [← same.2]
    exact ⟨by simpa only [work, Outcome.state] using reconstructed.growth,
      by simpa only [work, Outcome.state] using reconstructed.history⟩

private theorem first_node_publication
    {width count : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (left right result : Value Symbol Guard)
    (before after : SourceEqualityNativeDemand.State width)
    (actual : Trace count
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before
      (.code (.pure result)) after) :
    SourceRecursiveIntersectionThunks.NodeReady before.native.machine
      ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ∧
    ∃ (next : SourceRecursiveIntersectionCode.Code Symbol Guard (Value Symbol Guard))
        (first : SourceRecursiveIntersectionThunks.State width Symbol Guard) (tailFuel : Nat),
      SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
        (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native =
          .yielded next first ∧
      Trace tailFuel (.code next) ⟨first, before.operations⟩ (.code (.pure result)) after := by
  change Trace count (.code (.node
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)) before
    (.code (.pure result)) after at actual
  cases actual with
  | cons control state next reached final last tailFuel inputs one rest =>
      have ready : SourceRecursiveIntersectionThunks.NodeReady before.native.machine
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := inputs.1
      have lifted : SourceEqualityNativeDemand.lift before.operations
          (SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
            (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native) =
          .yielded next reached := by
        simpa only [SourceEqualityNativeDemand.step, requestNode,
          SourceSynthesisGeneralizeSyntax.top] using one
      cases observed : SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
          (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native with
      | yielded code native =>
          rw [observed] at lifted
          obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj lifted
          exact ⟨ready, code, native, tailFuel, rfl, rest⟩
      | done value native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted
      | failed failure native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted
      | blocked reason code native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted

/-- A completed retained filter query reaches the literal candidate-Type/goal native node instruction. -/
theorem current_filter_seeded_native_entry
    {Typing Key : Type} {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (narrowFuel : Nat)
    (narrowed : Value Symbol Guard) (narrowedHeap : State Symbol Guard)
    (narrowedCall : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      narrowFuel 0 rootValue sourceHeap = .done narrowed narrowedHeap)
    (rootRow : EdgeValue Symbol Guard)
    (rowMember : rootRow ∈ InternedEdgeResidency.nodeEdges narrowed)
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard)
    (seeded : Seeded rootRow.children [[0], [1, 0]] before result after) :
    Grows sourceHeap narrowedHeap ∧ Extends sourceHeap.nodes.issued narrowedHeap.nodes.issued ∧
    ∃ (goal candidate projected : Value Symbol Guard) (projectedHeap : State Symbol Guard),
      rootRow.entry.key.symbol = literal "filter" ∧
      rootRow.entry.key.constraint = filterGuard ∧ rootRow.children = [goal, candidate] ∧
      Available sourceHeap goal ∧ goal.free = [] ∧ Annotated (Origin (encodedLibrary lib)) goal ∧
      (∀ atom ∈ atoms goal, atom = .mu entry.identity) ∧
      SourceEqualityProjectionGraph.Forest [1, 0] [goal, candidate]
        before.native.machine.heap projected projectedHeap ∧
      let requestBefore := advancePhysical before ⟨projectedHeap, before.operations⟩
      SourceRecursiveIntersectionThunks.NodeReady requestBefore.native.machine
        ⟨IntersectionEmptyDomain.emptyDomain, projected, goal⟩ ∧
      ∃ (next : SourceRecursiveIntersectionCode.Code Symbol Guard (Value Symbol Guard))
          (first : SourceRecursiveIntersectionThunks.State width Symbol Guard) (tailFuel : Nat),
        SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
          (requestNode IntersectionEmptyDomain.emptyDomain projected goal) requestBefore.native =
            .yielded next first ∧
        Trace tailFuel (.code next) ⟨first, requestBefore.operations⟩ (.code (.pure result)) after := by
  have history := current_initial_narrowing_history lib query signed whole accepted rootValue sourceHeap built
    metadata holeKey fits admits narrowFuel narrowed narrowedHeap narrowedCall
  obtain ⟨_chunks, goal, candidate, candidateStart, _candidateAfter, _edgeAfter,
      _chunksRun, _wholeShape, symbol, constraint, children, goalBuilt,
      _candidateContext, _candidateBuilt, _edgeMade, _rootMade, _candidateGrowth, _factory⟩ :=
    SourceSynthesisCurrentFirstFilterSourceLink.current_narrowed_filter_interval
      lib query signed whole accepted rootValue sourceHeap built metadata holeKey fits admits
      narrowFuel narrowed narrowedHeap narrowedCall rootRow rowMember
  have originalMember := SourceSynthesisCurrentInitialOuterNarrowRows.initial_outer_narrow_rows
    lib query signed whole accepted rootValue sourceHeap built metadata holeKey fits admits
    narrowFuel narrowed narrowedHeap narrowedCall rootRow rowMember
  have checked := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)
  have sourceFacts : Facts sourceHeap := by simpa only [built, Outcome.state] using checked.facts
  have rootAvailable := checked.result rootValue sourceHeap built
  have rowResident := InternedEdgeResidency.resident_edges sourceHeap sourceFacts.linked
    rootValue rootAvailable.resident rootRow originalMember
  have goalAvailable : Available sourceHeap goal :=
    sourceFacts.cached.edges rootRow.entry.key rootRow rowResident goal
      (by rw [children]; exact List.mem_cons_self)
  have goalClosed := InternedFreshOrdinarySourceFreeNames.closed_free_empty
    (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) goal candidateStart goalBuilt
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
  have goalAnnotated := annotatedBuild.result goal candidateStart goalBuilt
  have goalAtoms := SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    goal goalAvailable goalClosed
  cases seeded with
  | nonempty fold =>
      change Fold rootRow.children [[1, 0], [0]] before result after at fold
      cases fold with
      | cons operand rest native =>
          rename_i projected _middle observedGoal _later nativeFuel
          cases rest with
          | one seed =>
              cases operand with
              | force projectedHeap projectedGraph =>
                  cases seed with
                  | force seedHeap seedGraph =>
                      have selected : SourceEqualityProjectionGraph.Forest [0] [goal, candidate]
                          projectedHeap observedGoal seedHeap := by
                        simpa only [children, advancePhysical, SourceRecursiveIntersectionThunks.advance] using seedGraph
                      have direct : SourceEqualityProjectionGraph.Forest [0] [goal, candidate]
                          projectedHeap goal projectedHeap := .selected rfl .root
                      obtain ⟨goalSame, heapSame⟩ := SourceEqualityProjectionAPI.forest_unique selected direct
                      rw [goalSame, heapSame] at native
                      have nativeCall : Trace nativeFuel
                          (.code (requestNode IntersectionEmptyDomain.emptyDomain projected goal))
                          (advancePhysical before ⟨projectedHeap, before.operations⟩)
                          (.code (.pure result)) after := by
                        simpa only [advancePhysical, SourceRecursiveIntersectionThunks.advance] using native
                      have publication := first_node_publication projected goal result _ after nativeCall
                      refine ⟨history.1, history.2, goal, candidate, projected, projectedHeap,
                        symbol, constraint, children, goalAvailable, goalClosed, goalAnnotated, goalAtoms, ?_,
                        publication⟩
                      simpa only [children] using projectedGraph

end MicroCFTA.SourceSynthesisCurrentFilterSeededNativeEntry
