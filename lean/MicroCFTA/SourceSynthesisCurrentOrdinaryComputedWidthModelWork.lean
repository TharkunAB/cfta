import MicroCFTA.SourceSynthesisCurrentOrdinarySharedModelWork
import MicroCFTA.SourceSynthesisCurrentInitialComputedRoom

/-!
# Current ordinary startup at an input-derived sufficient width

The original inputs select a sufficient mathematical word width.
One existing producer retains the complete initializer, worker, and startup.
The same returned build discharges its exact capacity test.
Fixed Haskell word capacity and whole enumeration remain separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentOrdinaryComputedWidthModelWork
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

variable {Typing : Type}
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The original admitted Program retains its complete checked startup at sufficient width. -/
theorem uses_computed_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (budget : Nat) (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
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
          (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap) globals ∧
        Facts heap ∧ Available heap value ∧
        SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
        Grows empty heap ∧ Cache.Extends (empty : State Symbol Constraint).nodes.issued heap.nodes.issued ∧
        SourceEqualityAnnotationHeap.Heap
          (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
        ∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready
            (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap).checked.operations.constraints (.live identity []) ∧
          value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
          let request : NodeRequest := ⟨emptyValue cache, value⟩
          let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
          let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap)
          let need := phaseNeed budget first (seed heap)
          ∃ result after,
            SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
              output.1 need need need need need need need need need budget request
              (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap) ∧
            (∀ fuel, output.1 ≤ fuel →
              nodeCall fuel need need need need need need need need need budget request
                (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap) = .done result after) ∧
            (∀ fuel, output.1 ≤ fuel →
              SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
                fuel need need need need need need need need need budget request
                (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap)) ∧
            ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
                (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap) result after,
              SourceCurrentAllocatedSharedPartialChecks.Checks
                (SourceCurrentAllocatedSharedPartialChecks.nodeCallTrace graph) ∧
              SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph globals final ∧
              Post formulas solver next (caller ((SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget) + 2) cache heap) after final ∧
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
  let selected := SourceSynthesisCurrentInitialComputedRoom.bits lib query (Int.ofNat program.components) budget
  obtain ⟨ordinary, source⟩ :=
    SourceSynthesisCurrentOrdinarySharedModelWork.uses_checked_native_initial
      formulas solver unpruned eligible covered selected budget metadata emptyPending ambient residualMeaning
  obtain ⟨expression, source⟩ := source
  obtain ⟨body, source⟩ := source
  obtain ⟨fields, source⟩ := source
  obtain ⟨cache, source⟩ := source
  obtain ⟨value, source⟩ := source
  obtain ⟨heap, source⟩ := source
  obtain ⟨built, source⟩ := source
  let whole : Term Symbol := .node (literal "filter") [candidateRigid query.queryGoal, body]
  dsimp only at source
  obtain ⟨returned, accepted, annotation, projected, decoded, counted, prepared, conjunctionFields,
      context, facts, available, roles, growth, issued, origins, identity, emptySame,
      inheritedReady, closed, original, complete⟩ := source
  have sourceAccepted : InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) whole := accepted
  have room := SourceSynthesisCurrentInitialComputedRoom.room_of_build lib query
    (Int.ofNat program.components) expression returned budget value heap built cache
  refine ⟨ordinary, expression, body, fields, cache, value, heap, built, ?_⟩
  exact ⟨returned, sourceAccepted, annotation, projected, decoded, counted, prepared, conjunctionFields,
    context, facts, available, roles, growth, issued, origins, identity, emptySame,
    inheritedReady, closed, original, complete room⟩

end MicroCFTA.SourceSynthesisCurrentOrdinaryComputedWidthModelWork
