import MicroCFTA.SourceSynthesisOrdinaryRelevantCompleteness
import MicroCFTA.SourceSynthesisOriginalCallerInitialization
import MicroCFTA.SourceSynthesisOriginalGuardsProjectable
import MicroCFTA.SourcePruningEnumerationInitialModelWork
import MicroCFTA.InternedGuardedExecution

/-!
# Ordinary admission at the same original native startup

One ordinary source certificate supplies its exact annotated term.
One original caller producer supplies the build and current context.
The same build supplies projectable guards and native term membership.
The existing startup producer supplies one packet and one assignment.
Its pending potential equals the native size of that same term.

The source uses an empty avoid list and exact query-token coverage.
The theorem does not bound annotation size by Program component count.
It does not execute native reduction or prove complete enumeration,
fixed-width runtime adequacy, or Haskell execution correspondence.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryInitialModelWork
open Language Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query Ty)
open SourceSynthesisFirstOrderConstruction (firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisOrdinaryRelevantCompleteness (UsesEligible)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals emptyValue)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax ProgramValue)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet)
open EnumerationCorrectness (Satisfies)
open EnumerationStorageProgress (pendingSize)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

variable {Typing : Type}
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Constraint)]

/-- Ordinary admission derives the full same-build startup packet and its exact model work. -/
theorem uses_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (width : Nat) (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body fields cache value heap,
        ∃ built : InternedFreshOrdinaryConstruction.build
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
        Context formulas solver (inventory (ordinarySymbols expression) value heap built)
          (caller width cache heap) globals ∧
        Facts heap ∧ Available heap value ∧ ProgramValue literal value ∧
        Grows empty heap ∧
        Cache.Extends (empty : State Symbol Constraint).nodes.issued heap.nodes.issued ∧
        (∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready
            (caller width cache heap).checked.operations.constraints (.live identity []) ∧
          value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value) ∧
        SourceEqualityAnnotationHeap.Heap
          (fun guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes) heap ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient value whole ∧
        ∃ handle,
          encodeNode value = some handle ∧
          lookupNode heap handle = some value ∧
          let startup : Cached :=
            ⟨EnumerationState.initial handle,
              fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
              fun _ => none⟩
          ((Packet formulas solver (inventory (ordinarySymbols expression) value heap built)
              (caller width cache heap) globals metadata startup ∧
            EnumerationValidity.Canonical startup.core ∧
            startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
            SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
            EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
            ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
              ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
            EnumerationCarriers.CarriesGraph startup.core 0 ∧
            EnumerationGraphReferences.ReferencesCarry startup.core) ∧
          ∃ assignment : Nat → Term Symbol,
            assignment 0 = whole ∧
            Satisfies (SourcePruningEnumerationNativeLanguage.handles
              (SourceEqualityPCSGuard.holds formulas solver) ambient heap)
              residualMeaning assignment startup.core ∧
            (∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group) ∧
            SourcePruningEnumerationOrigins.AssignmentOrigins whole startup.core.counter assignment ∧
            pendingSize startup.core assignment = NumberedTerms.size whole ∧
            pendingSize startup.core assignment ≤ NumberedTerms.size whole ∧
            SourcePruningEnumerationNativeWork.work (NumberedTerms.size whole) startup assignment =
              (NumberedTerms.size whole + 1) * NumberedTerms.size whole +
                (if MergedOrdinaryHeight.recursiveBoundary value then 0 else 1) := by
  obtain ⟨ordinary, expression, body, returned, accepted, annotation, projected, decoded, counted⟩ :=
    SourceSynthesisOrdinaryRelevantCompleteness.uses_root_member
      formulas solver unpruned eligible covered
  obtain ⟨fields, cache, value, heap, built, prepared, context, facts, available,
      roles, growth, issued, identity, emptySame, emptyReady, closed, original⟩ :=
    SourceSynthesisOriginalCallerInitialization.accepted lib query
      (Int.ofNat program.components) expression returned width Cache.emptyState Cache.empty_valid
      formulas solver
  let whole : Term Symbol := .node (literal "filter") [rigidTerm query.queryGoal, body]
  have projectable := SourceSynthesisOriginalGuardsProjectable.initial_heap
    lib query (Int.ofNat program.components) expression returned value heap built
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (mapSyntax literal expression) [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have nativeMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient value whole := by
    rw [InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact accepted
  obtain ⟨handle, encoded, found, retained, models⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_models_origins_work
      formulas solver (inventory (ordinarySymbols expression) value heap built)
      (caller width cache heap) globals metadata value context available closed emptyPending
  obtain ⟨assignment, assigned, satisfied, _refuted, origins, pending, bounded, work⟩ :=
    models (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning whole nativeMember
  have refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group := by
    intro group member
    rw [emptyPending] at member
    cases member
  exact ⟨ordinary, expression, body, fields, cache, value, heap, built,
    returned, accepted, annotation, projected, decoded, counted,
    prepared, context, facts, available, roles, growth, issued,
    ⟨identity, emptySame, emptyReady, closed, original⟩,
    projectable, nativeMember, handle, encoded, found, retained,
    assignment, assigned, satisfied, refuted, origins, pending, bounded, work⟩

end MicroCFTA.SourceSynthesisOrdinaryInitialModelWork
