import MicroCFTA.SourceSynthesisCurrentRelevantAdmission
import MicroCFTA.SourceSynthesisCurrentInitialModelWork
import MicroCFTA.InternedGuardedExecution

/-!
# Ordinary current witnesses at the same cold startup

Current admission supplies the original Program and its exact annotated term.
One current startup producer supplies the actual build, cache, and packet.
The same term supplies its model and exact initial work in that packet.
The startup precedes native worker execution. Annotation size remains separate
from Program component count and fixed-width execution resources.
-/
namespace MicroCFTA.SourceSynthesisCurrentOrdinaryInitialModelWork
open Language Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query Ty)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisPr210TypeReflection (candidateRigid)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisCurrentProgramAdmission (Eligible)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals emptyValue)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax ProgramValue)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet)
open EnumerationCorrectness (Satisfies)
open EnumerationStorageProgress (pendingSize)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
variable {Typing : Type}
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current ordinary admission retains the complete same-term cold startup and model-work packet. -/
theorem uses_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Guard → Term Symbol → Prop) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body fields cache value heap,
        ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
        let whole : Term Symbol := .node (literal "filter") [candidateRigid query.queryGoal, body]
        SourceSynthesisCurrentConstruction.firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) whole ∧
        whole.atPath [0] = some (candidateRigid query.queryGoal) ∧
        Projection literal Prod.fst whole program ∧ toProgram literal Prod.fst whole = program ∧
        (toProgram literal Prod.fst whole).components = program.components ∧
        SourceEqualityOriginalAllocationPreparation.Receipt
          (guards (ordinarySymbols expression)) initial fields cache ∧
        SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
        Context formulas solver (inventory (ordinarySymbols expression) value heap built)
          (caller width cache heap) globals ∧
        Facts heap ∧ Available heap value ∧ ProgramValue literal value ∧
        Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
        SourceEqualityAnnotationHeap.Heap
          (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
        (∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready
            (caller width cache heap).checked.operations.constraints (.live identity []) ∧
          value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value whole ∧
        ∃ handle,
          encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
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
          (∀ (otherHolds : Guard → Term Symbol → Bool) (otherAmbient : InternedGuardedLanguage.Env Symbol)
            (otherMeaning : Guard → Term Symbol → Prop) (otherTerm : Term Symbol),
            InternedGuardedLanguage.meaning otherHolds otherAmbient value otherTerm →
            ∃ (otherProgram : Program) (otherAssignment : Nat → Term Symbol),
              Projection literal Prod.fst otherTerm otherProgram ∧
              toProgram literal Prod.fst otherTerm = otherProgram ∧
              otherProgram.components = program.components ∧ otherAssignment 0 = otherTerm ∧
              Satisfies (SourcePruningEnumerationNativeLanguage.handles otherHolds otherAmbient heap)
                otherMeaning otherAssignment startup.core ∧
              (∀ group ∈ metadata.pending, SourcePruningResume.Refutes otherAssignment group) ∧
              SourcePruningEnumerationOrigins.AssignmentOrigins otherTerm startup.core.counter otherAssignment ∧
              pendingSize startup.core otherAssignment = NumberedTerms.size otherTerm ∧
              pendingSize startup.core otherAssignment ≤ NumberedTerms.size otherTerm ∧
              SourcePruningEnumerationNativeWork.work (NumberedTerms.size otherTerm) startup otherAssignment =
                (NumberedTerms.size otherTerm + 1) * NumberedTerms.size otherTerm +
                  (if MergedOrdinaryHeight.recursiveBoundary value then 0 else 1)) ∧
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
    SourceSynthesisCurrentRelevantAdmission.uses_root_member formulas solver unpruned eligible covered
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context, facts, available,
      roles, growth, issued, physicalOrigins, identity, emptySame, emptyReady, closed, original,
      handle, encoded, found, startupPacket, models⟩ :=
    SourceSynthesisCurrentInitialModelWork.accepted lib query (Int.ofNat program.components)
      expression returned width initial valid formulas solver metadata emptyPending
  let whole : Term Symbol := .node (literal "filter") [candidateRigid query.queryGoal, body]
  have mappedBuilt : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression)
      [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have nativeMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient value whole := by
    rw [InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact accepted
  obtain ⟨_otherProgram, assignment, _otherProjected, _otherDecoded, _otherCount, assigned,
      satisfied, refuted, assignmentOrigins, pending, bounded, work⟩ :=
    models (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning whole nativeMember
  refine ⟨ordinary, expression, body, fields, cache, value, heap, built,
    returned, accepted, annotation, projected, decoded, counted, prepared, conjunctionFields,
    context, facts, available, roles, growth, issued, physicalOrigins,
    ⟨identity, emptySame, emptyReady, closed, original⟩, nativeMember,
    handle, encoded, found, startupPacket, ?_, assignment, assigned, satisfied, refuted,
    assignmentOrigins, pending, bounded, work⟩
  simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast] using models

end MicroCFTA.SourceSynthesisCurrentOrdinaryInitialModelWork
