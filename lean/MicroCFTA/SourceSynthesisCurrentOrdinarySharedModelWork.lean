import MicroCFTA.SourceSynthesisCurrentRelevantAdmission
import MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion
import MicroCFTA.SourcePruningEnumerationInitialModelWork
import MicroCFTA.InternedGuardedExecution

/-!
# Current ordinary admission at the same checked shared startup

One current ordinary witness fixes the source term and Program.
One checked producer retains its complete initializer and worker endpoint.
The same returned NodeLaw retains the exact annotated witness.
One startup producer supplies its assignment, origins, and native work.
The actual computed Room condition remains explicit.
-/
namespace MicroCFTA.SourceSynthesisCurrentOrdinarySharedModelWork
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceSynthesisTypeSyntax (Library Query Ty)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisCurrentProgramAdmission (Eligible)
open SourceSynthesisPr210TypeReflection (candidateRigid)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceSynthesisGeneralizeSyntax (top)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue inventory globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet)
open EnumerationCorrectness (Satisfies)
open EnumerationStorageProgress (pendingSize)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover

private theorem meaning_decider_eq
    (first second : DecidableEq FullSyntax.Formula)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (value : Node) (term : Term Symbol) :
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula first formulas solver) ambient value term =
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula second formulas solver) ambient value term :=
  congrArg (fun decider : DecidableEq FullSyntax.Formula =>
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula decider formulas solver) ambient value term)
    (Subsingleton.elim first second)

variable {Typing : Type}
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Current ordinary admission retains the complete checked endpoint and its same-term startup. -/
theorem uses_checked_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (bits budget : Nat) (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body fields cache value heap,
        ∃ built : InternedFreshOrdinaryConstruction.build
            (ordinarySymbols expression) [] empty = .done value heap,
        let whole : Term Symbol := .node (literal "filter") [candidateRigid query.queryGoal, body]
        SourceSynthesisCurrentConstruction.firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) whole ∧
        whole.atPath [0] = some (candidateRigid query.queryGoal) ∧
        Projection literal Prod.fst whole program ∧
        toProgram literal Prod.fst whole = program ∧
        (toProgram literal Prod.fst whole).components = program.components ∧
        SourceEqualityOriginalAllocationPreparation.Receipt
          (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
        SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
        Context formulas solver (inventory (ordinarySymbols expression) value heap built)
          (caller (bits + 2) cache heap) globals ∧
        Facts heap ∧ Available heap value ∧
        SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
        Grows empty heap ∧ Cache.Extends (empty : State Symbol Constraint).nodes.issued heap.nodes.issued ∧
        SourceEqualityAnnotationHeap.Heap
          (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
        ∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready
            (caller (bits + 2) cache heap).checked.operations.constraints (.live identity []) ∧
          value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
          let request : NodeRequest := ⟨emptyValue cache, value⟩
          let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
          let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
          let need := phaseNeed budget first (seed heap)
          Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) →
          ∃ result after,
            SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
              output.1 need need need need need need need need need budget request
              (caller (bits + 2) cache heap) ∧
            (∀ fuel, output.1 ≤ fuel →
              nodeCall fuel need need need need need need need need need budget request
                (caller (bits + 2) cache heap) = .done result after) ∧
            (∀ fuel, output.1 ≤ fuel →
              SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
                fuel need need need need need need need need need budget request
                (caller (bits + 2) cache heap)) ∧
            ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
                (caller (bits + 2) cache heap) result after,
              SourceCurrentAllocatedSharedPartialChecks.Checks
                (SourceCurrentAllocatedSharedPartialChecks.nodeCallTrace graph) ∧
              SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph globals final ∧
              Post formulas solver next (caller (bits + 2) cache heap) after final ∧
              Frame formulas solver next after.checked ∧
              Fits (forecast budget first (seed heap)).2 after.checked ∧
              SourceEqualityAnnotationHeap.Heap
                (fun guard => guard ∈ (forecast budget first (seed heap)).1) after.checked.native.machine.heap ∧
              Available after.checked.native.machine.heap result ∧
              SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
              SharedReady (encodedLibrary lib) (initialShared after.checked after.merge) ∧
              GuardHeap (Origin (encodedLibrary lib)) after.checked.native.machine.heap ∧
              History (encodedLibrary lib) literal after ∧ result.free = [] ∧
              NodeFields (encodedLibrary lib) literal request result ∧
              ValueFields (Origin (encodedLibrary lib)) literal result ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value whole ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result whole ∧
              ∃ handle,
                encodeNode result = some handle ∧
                lookupNode after.checked.native.machine.heap handle = some result ∧
                let startup : Cached :=
                  ⟨EnumerationState.initial handle,
                    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary result else false,
                    fun _ => none⟩
                ((Packet formulas solver next after final metadata startup ∧
                  EnumerationValidity.Canonical startup.core ∧
                  startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
                  SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
                  EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
                  ∀ slot, SourcePruningEnumerationNativeIndex.candidate after.checked.native.machine.heap
                    ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
                  EnumerationCarriers.CarriesGraph startup.core 0 ∧
                  EnumerationGraphReferences.ReferencesCarry startup.core) ∧
                ∃ assignment : Nat → Term Symbol,
                  assignment 0 = whole ∧
                  Satisfies (SourcePruningEnumerationNativeLanguage.handles
                    (SourceEqualityPCSGuard.holds formulas solver) ambient after.checked.native.machine.heap)
                    residualMeaning assignment startup.core ∧
                  (∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group) ∧
                  SourcePruningEnumerationOrigins.AssignmentOrigins whole startup.core.counter assignment ∧
                  pendingSize startup.core assignment = NumberedTerms.size whole ∧
                  pendingSize startup.core assignment ≤ NumberedTerms.size whole ∧
                  SourcePruningEnumerationNativeWork.work (NumberedTerms.size whole) startup assignment =
                    (NumberedTerms.size whole + 1) * NumberedTerms.size whole +
                      (if MergedOrdinaryHeight.recursiveBoundary result then 0 else 1) := by
  obtain ⟨ordinary, expression, body, returned, accepted, annotation, projected, decoded, counted⟩ :=
    SourceSynthesisCurrentRelevantAdmission.uses_root_member
      formulas solver unpruned eligible covered
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, inheritedReady,
      closed, original, complete⟩ :=
    SourceSynthesisCurrentCheckedHereditarySharedCompletion.accepted lib query
      (Int.ofNat program.components) expression returned bits budget formulas solver
  let whole : Term Symbol := .node (literal "filter") [candidateRigid query.queryGoal, body]
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
  refine ⟨ordinary, expression, body, fields, cache, value, heap, built,
    returned, accepted, annotation, projected, decoded, counted, prepared, conjunctionFields,
    context, facts, available, roles, growth, issued, origins, identity, emptySame,
    inheritedReady, closed, original, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, baseRanges, done, allRanges, next, final, graph,
      checks, reads, post, afterFrame, afterFits, afterKnown, resultAvailable, law,
      typed, muGuards, history, resultClosed, nodeFields, valueFields⟩ := complete room
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (mapSyntax literal expression) [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have originalMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient value whole := by
    rw [InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact accepted
  have inherited : SourceEqualityPrecheck.Sat whole request.inherited.payload := by
    change SourceEqualityPrecheck.Sat whole (emptyValue cache).payload
    rw [emptySame]
    simp [SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat,
      EqualityNormalize.Satisfies]
  have canonicalResult := ((law ambient whole).2 inherited).mpr
    (Eq.mp (meaning_decider_eq _ _ formulas solver ambient value whole) originalMember)
  have resultMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient result whole :=
    Eq.mp (meaning_decider_eq _ _ formulas solver ambient result whole) canonicalResult
  obtain ⟨handle, encoded, found, retained, models⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_models_origins_work
      formulas solver next after final metadata result post.context resultAvailable resultClosed emptyPending
  obtain ⟨assignment, assigned, satisfied, _refuted, assignmentOrigins, pending, bounded, work⟩ :=
    models (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning whole resultMember
  have refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group := by
    intro group member
    rw [emptyPending] at member
    cases member
  exact ⟨result, after, baseRanges, done, allRanges, next, final, graph,
    checks, reads, post, afterFrame, afterFits, afterKnown, resultAvailable, law,
    typed, muGuards, history, resultClosed, nodeFields, valueFields,
    originalMember, resultMember, handle, encoded, found, retained,
    assignment, assigned, satisfied, refuted, assignmentOrigins, pending, bounded, work⟩

end MicroCFTA.SourceSynthesisCurrentOrdinarySharedModelWork
