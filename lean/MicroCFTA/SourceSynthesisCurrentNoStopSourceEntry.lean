import MicroCFTA.SourceSynthesisCurrentCallerInitialization
import MicroCFTA.SourceSynthesisCurrentInitialEagerInvocation
import MicroCFTA.SourceSynthesisCurrentCandidateAppOperands

/-!
# The real no-stop source entry

The accepted source root is empty or an ordinary node.
The original initializer constructs its cold caller and source inventory.
The no-stop selector therefore expands slot zero.
The configured eager entry retains the real outer narrowing operation.
This result does not supply the selected-prefix branch observation.
-/
namespace MicroCFTA.SourceSynthesisCurrentNoStopSourceEntry
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem source_root_ordinary
    [DecidableEq (EdgeKey Symbol Constraint)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap) :
    SourceEqualityRequiredCache.Ordinary rootValue := by
  obtain ⟨_chunks, _chunksRun, wholeShape, _factory⟩ :=
    SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands
      lib query signed whole accepted
  have rootSyntax : ∃ rows : List (EdgeSyntax Symbol Constraint), ordinarySymbols whole = .node rows := by
    rw [wholeShape]
    exact ⟨_, rfl⟩
  obtain ⟨sourceRows, sourceShape⟩ := rootSyntax
  have nodeBuilt := built
  rw [sourceShape, build] at nodeBuilt
  have checked := InternedFreshOrdinaryFacts.buildEdges_verified sourceRows []
    (empty : InternedConstructorTemplates.State Symbol Constraint) empty_facts
    (by intro value member; cases member)
  cases rowsDone : buildEdges sourceRows [] (empty : InternedConstructorTemplates.State Symbol Constraint) with
  | pending key state =>
      simp only [rowsDone, Outcome.bind] at nodeBuilt
      cases nodeBuilt
  | done rows middle =>
      have same : (run (makeNode rows) middle).1 = rootValue ∧
          (run (makeNode rows) middle).2 = sourceHeap := by
        apply Outcome.done.inj
        simpa only [rowsDone, Outcome.bind, work] using nodeBuilt
      have middleFacts : Facts middle := by
        simpa only [rowsDone, Outcome.state] using checked.facts
      rw [← same.1]
      exact SourceEqualityRequiredCache.node_ordinary rows middle middleFacts
        (checked.result rows middle rowsDone)

/-- Original source initialization derives the exact real no-stop eager entry at slot zero. -/
theorem accepted_no_stop_eager_entry
    {Typing Key : Type} {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) :
    ∃ fields cache,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols whole)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) sourceHeap ∧
      Context formulas solver
        (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols whole) rootValue sourceHeap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap)
        SourceCurrentAllocatedPartialInitialization.globals ∧
      sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      MergedOrdinaryHeight.recursiveBoundary rootValue = false ∧
      ∃ handle : Nat, encodeNode rootValue = some handle ∧ lookupNode sourceHeap handle = some rootValue ∧
        let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
        let startup : Cached := ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
          fun _ => none⟩
        SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup = some (.expand 0) ∧
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager
          holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
          workFuel recursiveFuel metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup =
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel InternedEdgeResidency.nodeEdges)
          holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
          workFuel recursiveFuel metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup
          (some (.expand 0)) := by
  obtain ⟨fields, cache, initValue, initHeap, initBuilt, prepared, fieldFacts, context, facts,
      available, _program, _growth, _issued, _origins, _identity, _emptyValue, _emptyReady,
      closed, _original⟩ :=
    SourceSynthesisCurrentCallerInitialization.accepted lib query signed whole accepted
      width Cache.emptyState Cache.empty_valid formulas solver
  have same := Outcome.done.inj (initBuilt.symm.trans built)
  have valueSame : initValue = rootValue := same.1
  have heapSame : initHeap = sourceHeap := same.2
  subst initValue
  subst initHeap
  have rootOrdinary := source_root_ordinary lib query signed whole accepted rootValue sourceHeap built
  have clear : MergedOrdinaryHeight.recursiveBoundary rootValue = false := by
    cases rootValue <;> first | rfl | cases rootOrdinary
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    sourceHeap rootValue facts.coherent available closed
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
  let startup : Cached := ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
    fun _ => none⟩
  have decision : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup =
      some (.expand 0) := by
    simp [SourcePruningEnumerationRestart.decision, EnumerationPureSelection.next,
      EnumerationPureSelection.find, EnumerationIndexSelection.candidates,
      EnumerationState.pickNext, startup, EnumerationState.initial, clear]
  refine ⟨fields, cache, prepared, fieldFacts, context, stored, clear, handle, encoded, decoded, decision, ?_⟩
  change SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager
      holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
      workFuel recursiveFuel metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup =
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel InternedEdgeResidency.nodeEdges)
      holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
      workFuel recursiveFuel metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup
      (some (.expand 0))
  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager,
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow,
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow,
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, decision]

end MicroCFTA.SourceSynthesisCurrentNoStopSourceEntry
