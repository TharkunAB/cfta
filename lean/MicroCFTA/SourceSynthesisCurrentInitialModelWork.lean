import MicroCFTA.SourceSynthesisCurrentCallerInitialization
import MicroCFTA.SourceSynthesisOriginalProgramTermSize
import MicroCFTA.SourcePruningEnumerationInitialModelWork

/-!
# Complete cold startup from current source output

One current initializer supplies the actual build, cache, and Context.
One startup producer supplies its complete packet at that same raw value.
Each accepted term retains its Program count and exact initial model work.
No worker executes here. Room and hereditary Type fields remain separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialModelWork
open Language Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals emptyValue)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax ProgramValue)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current success retains the full initializer and same-value startup with counted model work. -/
theorem accepted (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller width cache heap) globals ∧
      Facts heap ∧ Available heap value ∧ ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (caller width cache heap).checked.operations.constraints (.live identity []) ∧
        value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
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
          ∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
            (residualMeaning : Guard → Term Symbol → Prop) (term : Term Symbol),
            InternedGuardedLanguage.meaning holds ambient value term →
            ∃ (program : Program) (assignment : Nat → Term Symbol),
              Projection literal Prod.fst term program ∧ toProgram literal Prod.fst term = program ∧
              program.components = signed.toNat ∧ assignment 0 = term ∧
              Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
                residualMeaning assignment startup.core ∧
              (∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group) ∧
              SourcePruningEnumerationOrigins.AssignmentOrigins term startup.core.counter assignment ∧
              pendingSize startup.core assignment = NumberedTerms.size term ∧
              pendingSize startup.core assignment ≤ NumberedTerms.size term ∧
              SourcePruningEnumerationNativeWork.work (NumberedTerms.size term) startup assignment =
                (NumberedTerms.size term + 1) * NumberedTerms.size term +
                  (if MergedOrdinaryHeight.recursiveBoundary value then 0 else 1) := by
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original⟩ :=
    SourceSynthesisCurrentCallerInitialization.accepted lib query signed expression returned
      width initial valid formulas solver
  obtain ⟨handle, encoded, decoded, startupPacket, models⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_models_origins_work formulas solver
      (inventory (ordinarySymbols expression) value heap built) (caller width cache heap) globals
      metadata value context available closed emptyPending
  have mappedBuilt : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression)
      [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have sourceStructure :=
    SourceSynthesisCurrentProgramStructure.current_root_structure lib query signed expression returned
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context, facts,
    available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original,
    handle, encoded, decoded, startupPacket, ?_⟩
  intro holds ambient residualMeaning term accepted
  obtain ⟨program, projected, programDecoded, counted⟩ :=
    SourceSynthesisOriginalProgramTermSize.build_accepted literal Prod.fst sourceStructure.2
      value heap mappedBuilt holds ambient term accepted
  obtain ⟨assignment, rootTerm, satisfied, _refuted, assignmentOrigins, pending, bound, work⟩ :=
    models holds ambient residualMeaning term accepted
  have refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group := by
    intro group member
    rw [emptyPending] at member
    cases member
  exact ⟨program, assignment, projected, programDecoded, counted, rootTerm, satisfied,
    refuted, assignmentOrigins, pending, bound, work⟩

end MicroCFTA.SourceSynthesisCurrentInitialModelWork
