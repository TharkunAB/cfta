import MicroCFTA.SourceSynthesisOrdinaryRelevantCompleteness
import MicroCFTA.SourceSynthesisOriginalCheckedSharedProgramCount
import MicroCFTA.SourcePruningEnumerationInitialModelWork
import MicroCFTA.InternedGuardedExecution

/-!
# Ordinary admission at the same checked shared startup

One ordinary source certificate supplies the exact annotated term.
One checked shared completion supplies its original build and worker return.
The same empty inherited value lets NodeLaw retain that exact term.
The startup producer uses the returned caller, inventory and full memos.
It supplies one assignment with exact initial pending and work values.

The computed Room condition remains explicit.
The returned Mu guard-profile law keeps its existing meaning.
It does not state projectability of all physical edge guards.
Native annotation size is separate from Program component count.
Whole enumeration and Haskell execution correspondence remain separate.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryCheckedInitialModelWork
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query Ty)
open SourceSynthesisFirstOrderConstruction (firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisOrdinaryRelevantCompleteness (UsesEligible)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
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

/-- Ordinary admission retains the full checked worker packet and the same term's startup work. -/
theorem uses_checked_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (bits budget : Nat) (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body fields cache value heap,
        ∃ _built : InternedFreshOrdinaryConstruction.build
            (ordinarySymbols expression) [] empty = .done value heap,
        let whole : Term Symbol := .node (literal "filter") [rigidTerm query.queryGoal, body]
        firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) whole ∧
        whole.atPath [0] = some (rigidTerm query.queryGoal) ∧
        Projection literal Prod.fst whole program ∧
        toProgram literal Prod.fst whole = program ∧
        (toProgram literal Prod.fst whole).components = program.components ∧
        SourceEqualityOriginalAllocationPreparation.Receipt
          (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression))
          Cache.emptyState fields cache ∧
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
            SharedReady lib (initialShared after.checked after.merge) ∧
            GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
            result.free = [] ∧ NodeFields lib literal request result ∧ ValueFields (Origin lib) literal result ∧
            (∀ otherAmbient term,
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) otherAmbient result term →
              ∃ projectedProgram, Projection literal Prod.fst term projectedProgram ∧
                toProgram literal Prod.fst term = projectedProgram ∧
                projectedProgram.components = (Int.ofNat program.components).toNat) ∧
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
    SourceSynthesisOrdinaryRelevantCompleteness.uses_root_member
      formulas solver unpruned eligible covered
  obtain ⟨fields, cache, value, heap, built, prepared, complete⟩ :=
    SourceSynthesisOriginalCheckedSharedProgramCount.accepted lib query
      (Int.ofNat program.components) expression returned bits budget formulas solver
  let whole : Term Symbol := .node (literal "filter") [rigidTerm query.queryGoal, body]
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
  refine ⟨ordinary, expression, body, fields, cache, value, heap, built,
    returned, accepted, annotation, projected, decoded, counted, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, baseRanges, done, allRanges, next, final, graph,
      checks, reads, post, afterFrame, afterFits, afterKnown, available, law,
      typed, muGuards, history, closed, nodeFields, valueFields, programCounts⟩ := complete room
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (mapSyntax literal expression) [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have originalMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient value whole := by
    rw [InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact accepted
  have inherited : SourceEqualityPrecheck.Sat whole request.inherited.payload := by
    obtain ⟨identity, same⟩ := SourceCurrentAllocatedPartialInitialization.emptyValue_live cache
    change SourceEqualityPrecheck.Sat whole (emptyValue cache).payload
    rw [same]
    simp [SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat,
      EqualityNormalize.Satisfies]
  have canonicalResult := ((law ambient whole).2 inherited).mpr
    (Eq.mp (meaning_decider_eq _ _ formulas solver ambient value whole) originalMember)
  have resultMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient result whole :=
    Eq.mp (meaning_decider_eq _ _ formulas solver ambient result whole) canonicalResult
  have publicProgramCounts : ∀ otherAmbient term,
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) otherAmbient result term →
      ∃ projectedProgram, Projection literal Prod.fst term projectedProgram ∧
        toProgram literal Prod.fst term = projectedProgram ∧
        projectedProgram.components = (Int.ofNat program.components).toNat := by
    intro otherAmbient term member
    exact programCounts otherAmbient term
      (Eq.mp (meaning_decider_eq _ _ formulas solver otherAmbient result term) member)
  obtain ⟨handle, encoded, found, retained, models⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_models_origins_work
      formulas solver next after final metadata result post.context available closed emptyPending
  obtain ⟨assignment, assigned, satisfied, _refuted, origins, pending, bounded, work⟩ :=
    models (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning whole resultMember
  have refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group := by
    intro group member
    rw [emptyPending] at member
    cases member
  exact ⟨result, after, baseRanges, done, allRanges, next, final, graph,
    checks, reads, post, afterFrame, afterFits, afterKnown, available, law,
    typed, muGuards, history, closed, nodeFields, valueFields, publicProgramCounts,
    originalMember, resultMember, handle, encoded, found, retained,
    assignment, assigned, satisfied, refuted, origins, pending, bounded, work⟩

end MicroCFTA.SourceSynthesisOrdinaryCheckedInitialModelWork
