import MicroCFTA.SourceSynthesisCurrentInitialEagerInvocation
import MicroCFTA.SourceSynthesisCurrentZeroProgramObstruction
import MicroCFTA.InternedFreshOrdinaryDepthComposition

/-!
# Actual emitted outputs at zero recursive depth

Status: UNCOMPILED CANDIDATE.
The current source root has an ordinary outer record or is empty.
The actual zero-depth worker stops before it emits that root.
The concrete size-zero source also rejects at every recursive depth.
The full finite joint-assignment target remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourcePruningEnumerationSharedPreparedRecursive (emitted)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem current_root_nonrecursive
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap) :
    MergedOrdinaryHeight.recursiveBoundary rootValue = false := by
  obtain ⟨_chunks, _chunksRun, wholeShape, _factory⟩ :=
    SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands
      lib query signed whole accepted
  obtain ⟨sourceRows, sourceShape⟩ :
      ∃ rows, ordinarySymbols whole = .node rows := by
    rw [wholeShape]
    exact ⟨_, rfl⟩
  have nodeBuilt := built
  rw [sourceShape, build] at nodeBuilt
  have checked := InternedFreshOrdinaryFacts.buildEdges_verified sourceRows []
    (empty : State Symbol Guard) empty_facts (by intro value member; cases member)
  have ordinary : SourceEqualityRequiredCache.Ordinary rootValue := by
    cases rowsDone : buildEdges sourceRows [] (empty : State Symbol Guard) with
    | pending key state =>
        simp only [rowsDone, Outcome.bind] at nodeBuilt
        cases nodeBuilt
    | done rows middle =>
        have same :
            (run (makeNode rows) middle).1 = rootValue ∧
              (run (makeNode rows) middle).2 = heap := by
          apply Outcome.done.inj
          simpa only [rowsDone, Outcome.bind, InternedNestedConstruction.work] using nodeBuilt
        have middleFacts : Facts middle := by
          simpa only [rowsDone, Outcome.state] using checked.facts
        rw [← same.1]
        exact SourceEqualityRequiredCache.node_ordinary rows middle middleFacts
          (checked.result rows middle rowsDone)
  cases rootValue with
  | empty | node => rfl
  | reference | union | mu => cases ordinary

/-- Every accepted current source emits nothing at zero recursive worker depth. -/
theorem current_zero_depth_emitted_nil
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (handle width : Nat)
    (graph : EnumerationState.Graph Symbol Guard) (checkEmpty : Bool) (workFuel : Nat) :
    let metadata : Metadata Unit := ⟨[], [], [], ()⟩
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    emitted (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (fun _ _ _ node state => .done node state)
      graph [] checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
      workFuel 0 metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup) = [] := by
  dsimp only
  have boundary := current_root_nonrecursive lib query signed whole accepted rootValue heap built
  have chosen : SourcePruningEnumerationRestart.decision none
      (fun (_ : Metadata Unit) _ => none) (⟨[], [], [], ()⟩ : Metadata Unit)
      (⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩ : Cached) = some (.expand 0) := by
    simp [SourcePruningEnumerationRestart.decision, EnumerationPureSelection.next,
      EnumerationPureSelection.find, EnumerationIndexSelection.candidates,
      EnumerationState.initial, EnumerationState.pickNext, boundary]
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  rw [chosen]
  rfl

/-- The concrete library has no components or argument-only rows. -/
def zeroLibrary : Library := ⟨[], [], [], .firstOrder⟩

/-- The concrete query has no arguments and requests one rigid type variable. -/
def zeroQuery : Query := ⟨[], .tVar "a"⟩

/-- The zero-size source keeps its actual filter and empty candidate union. -/
def zeroExpression : Expression :=
  SourceSynthesisFirstOrderConstruction.ofType (.union [])
    (SourceSynthesisCurrentContext.typeNode zeroQuery.queryGoal)

/-- The actual frontend accepts this concrete source at size zero. -/
theorem zero_source_accepted :
    SourceSynthesisCurrentConstruction.firstOrderRaw zeroLibrary zeroQuery (0 : Int) =
      .ok zeroExpression := by
  have arguments :
      (SourceSynthesisCurrentContext.context zeroLibrary zeroQuery).argumentEdges = [] := by
    rfl
  have relevant : SourceSynthesisFirstOrderConstruction.relevantRows
      (SourceSynthesisCurrentContext.context zeroLibrary zeroQuery) true 0 [] = .ok [] := by
    simp [SourceSynthesisFirstOrderConstruction.relevantRows,
      SourceSynthesisFirstOrderConstruction.resolveArguments,
      SourceSynthesisSelections.resolveSelection_empty,
      SourceSynthesisFirstOrderConstruction.termsRows]
  simp [SourceSynthesisCurrentConstruction.firstOrderRaw, arguments,
    SourceSynthesisSelections.permutations_nil, relevant, zeroExpression]

/-- Every actual native build of that source returns the empty root. -/
theorem zero_source_native_empty
    (rootValue : Node) (heap : State Symbol Guard)
    (built : build (ordinarySymbols zeroExpression) [] empty = .done rootValue heap) :
    rootValue = .empty := by
  have actual := InternedFreshOrdinaryDepthComposition.source_empty
    (ordinarySymbols zeroExpression) ([] : List InternedBinderProtocol.Reference)
    empty InternedFreshOrdinaryContext.empty_context rootValue heap built
  have shape :
      (InternedDepthSemantics.evaluate (ordinarySymbols zeroExpression)
        ([] : List (InternedDepthSemantics.Shape InternedBinderProtocol.Reference))).isEmpty = true := by
    simp [zeroExpression, SourceSynthesisFirstOrderConstruction.ofType, ordinarySymbols,
      SourceSynthesisUniverseCallerBoundary.ordinaryEdges,
      SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
      InternedDepthSemantics.evaluate, InternedDepthSemantics.evaluateEdges,
      InternedDepthSemantics.evaluateMany, InternedDepthSemantics.edge,
      InternedDepthSemantics.combine, InternedDepthSemantics.combineMany,
      InternedDepthSemantics.Shape.isEmpty]
  exact (InternedEmptyNormalization.reference_empty rootValue).mp
    (beq_iff_eq.mp (actual.trans shape))

/-- The actual built zero-size root has no finite native member. -/
theorem zero_source_no_native_member
    (rootValue : Node) (heap : State Symbol Guard)
    (built : build (ordinarySymbols zeroExpression) [] empty = .done rootValue heap)
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Language.Term Symbol) :
    ¬InternedGuardedLanguage.meaning holds ambient rootValue term := by
  rw [zero_source_native_empty rootValue heap built]
  intro impossible
  simpa only [InternedGuardedLanguage.meaning] using impossible

private theorem empty_initial_identity_emitted_nil
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (heap : State Symbol Guard)
    (width : Nat) (graph : EnumerationState.Graph Symbol Guard) (checkEmpty : Bool)
    (workFuel depth : Nat) :
    let metadata : Metadata Unit := ⟨[], [], [], ()⟩
    let startup : Cached :=
      ⟨EnumerationState.initial 0, fun slot => if slot = 0 then true else false, fun _ => none⟩
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    emitted (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (fun _ _ _ node state => .done node state)
      graph [] checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
      workFuel depth metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup) = [] := by
  cases depth with
  | zero => rfl
  | succ smaller => cases workFuel <;> rfl

/-- The same accepted size-zero initializer emits nothing at every supplied worker depth. -/
theorem zero_source_initializer_emitted_nil
    (rootValue : Node) (heap : State Symbol Guard)
    (built : build (ordinarySymbols zeroExpression) [] empty = .done rootValue heap)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (handle width : Nat)
    (encoded : SourcePruningEnumerationNodes.encodeNode rootValue = some handle)
    (graph : EnumerationState.Graph Symbol Guard) (checkEmpty : Bool) (workFuel depth : Nat) :
    let metadata : Metadata Unit := ⟨[], [], [], ()⟩
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    emitted (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (fun _ _ _ node state => .done node state)
      graph [] checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
      workFuel depth metadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup) = [] := by
  have emptyRoot := zero_source_native_empty rootValue heap built
  subst rootValue
  have handleZero : handle = 0 := (Option.some.inj encoded).symm
  subst handle
  exact empty_initial_identity_emitted_nil cache heap width graph checkEmpty workFuel depth

end MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity

#check @MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.current_zero_depth_emitted_nil
#print axioms MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.current_zero_depth_emitted_nil

#check @MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_accepted
#print axioms MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_accepted

#check @MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_native_empty
#print axioms MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_native_empty

#check @MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_no_native_member
#print axioms MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_no_native_member

#check @MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_initializer_emitted_nil
#print axioms MicroCFTA.SourceSynthesisCurrentZeroDepthProductivity.zero_source_initializer_emitted_nil
