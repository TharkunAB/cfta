import MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefixStable
import MicroCFTA.SourcePruningEnumerationIdentityWorkerMetadataErasure
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourceSynthesisProgramTermSize

set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisCurrentInitialIdentityMetadataErasure
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open EnumerationState (Graph)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Core" => EnumerationState.State Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
attribute [local instance] SourcePruningEnumerationAction.actionMonadList
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]


open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
open SourcePruningEnumerationIdentityResultMetadataErasure
  (eraseOutput eraseResult runEager_identity_metadata_erasure)

/-- Retain one current initializer and pair its actual identity-worker outputs after erasure. -/
theorem accepted_initial_identity_worker_erasure {Typing : Type}
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ValueFields (Origin (encodedLibrary lib)) literal value ∧
        ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
          ProgramSlots (Origin (encodedLibrary lib)) literal heap
            (EnumerationState.initial handle) (fun uv => uv = 0) ∧
          let caller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
          let startup : Cached :=
            ⟨EnumerationState.initial handle,
              fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
              fun _ => none⟩
          let metadata : Metadata Unit := ⟨[], [], [], ()⟩
          SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup =
            some (if MergedOrdinaryHeight.recursiveBoundary value then .done else .expand 0) ∧
          (value = .empty → ∀ (graph : Graph Symbol Guard) extra nativeFuel representativeFuel indexFuel callbackFuel,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow (fun _ _ _ node state => .done node state)
              graph [] none (fun _ _ => none) metadata (extra + 1) (extra + 1)
                nativeFuel representativeFuel indexFuel callbackFuel
              0 caller startup SourceCurrentAllocatedPartialInitialization.globals.query =
            .narrowed (EnumerationState.initial handle)
              (.done (value, some (EnumerationState.reject : EnumerationState.EnumerateM Symbol Guard Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
                caller.fourth caller.merge)
              SourceCurrentAllocatedPartialInitialization.globals.query (some []) none none none) ∧
          (value ≠ .empty → ∀ (graph : Graph Symbol Guard) extra nativeFuel representativeFuel indexFuel callbackFuel,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow (fun _ _ _ node state => .done node state)
              graph [] none (fun _ _ => none) metadata (extra + 1) (extra + 1)
                nativeFuel representativeFuel indexFuel callbackFuel
              0 caller startup SourceCurrentAllocatedPartialInitialization.globals.query =
            .narrowed (EnumerationState.initial handle)
              (.done (value, some (pure () : EnumerationState.EnumerateM Symbol Guard Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
                caller.fourth caller.merge)
              SourceCurrentAllocatedPartialInitialization.globals.query
              (some [.ok ((), EnumerationState.initial handle)])
              (some (EnumerationExpandableIndex.frame (EnumerationState.initial handle) startup))
              (some [.ok ((false, metadata), EnumerationState.initial handle)]) none) ∧
          (∀ uv, SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup = some (.expand uv) →
            uv = 0 ∧ MergedOrdinaryHeight.recursiveBoundary value = false) ∧
          ∀ (graph : Graph Symbol Guard) (checkEmpty : Bool)
            (edgesOf : Node → List (EdgeValue Symbol Guard)) (workFuel : Nat)
            (initialMetadata : Metadata Typing) (unitMetadata : Metadata Unit),
            let actual := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
              (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
              none (fun _ _ => none) workFuel depth initialMetadata caller
              SourceCurrentAllocatedPartialInitialization.globals.query startup
            let reference := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
              (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
              none (fun _ _ => none) workFuel depth unitMetadata caller
              SourceCurrentAllocatedPartialInitialization.globals.query startup
            SourcePruningEnumerationIdentityResultMetadataErasure.eraseResult actual =
              SourcePruningEnumerationIdentityResultMetadataErasure.eraseResult reference ∧
            ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted actual,
              ∃ referenceOutput ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted reference,
                SourcePruningEnumerationIdentityResultMetadataErasure.eraseOutput output =
                  SourcePruningEnumerationIdentityResultMetadataErasure.eraseOutput referenceOutput ∧
                referenceOutput.cache = output.cache ∧
                referenceOutput.caller = output.caller ∧
                referenceOutput.queries = output.queries ∧
                ∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                  (after : Core) (program : SourceSynthesisProgramTermSize.Program),
                  ((∀ extra, ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                      output.caller.checked.native.machine.heap (readFuel + extra) output.cache.core) =
                      [.ok (actualPartial, after)]) ∧
                    SourceSynthesisProgramTermSize.Projection literal Prod.fst
                      (SourcePruningPositions.openProgram true actualPartial) program) →
                  ((∀ extra, ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                      referenceOutput.caller.checked.native.machine.heap (readFuel + extra)
                      referenceOutput.cache.core) = [.ok (actualPartial, after)]) ∧
                    SourceSynthesisProgramTermSize.Projection literal Prod.fst
                      (SourcePruningPositions.openProgram true actualPartial) program) := by
  let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
      closed, original, valueFields, handle, encoded, decoded, slots,
      decision, emptyCase, nonemptyCase, chosen⟩ :=
    SourceSynthesisCurrentInitialIdentityPrefixStable.accepted_initial_identity_prefix_stable
      lib query signed expression returned depth formulas solver
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
    closed, original, valueFields, handle, encoded, decoded, slots,
    decision, emptyCase, nonemptyCase, chosen, ?_⟩
  intro graph checkEmpty edgesOf workFuel initialMetadata unitMetadata
  let caller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
      fun _ => none⟩
  let actual := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
    none (fun _ _ => none) workFuel depth initialMetadata caller
    SourceCurrentAllocatedPartialInitialization.globals.query startup
  let reference := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
    none (fun _ _ => none) workFuel depth unitMetadata caller
    SourceCurrentAllocatedPartialInitialization.globals.query startup
  have erasedSame : eraseResult actual = eraseResult reference :=
    runEager_identity_metadata_erasure graph checkEmpty edgesOf workFuel depth
      initialMetadata unitMetadata caller SourceCurrentAllocatedPartialInitialization.globals.query startup
  have erasedEmitted {T : Type}
      (observed : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
        (Output (bits + 2) T) (Failure (bits + 2) T) (bits + 2)) :
      emitted (eraseResult observed) = (emitted observed).map eraseOutput := by
    cases observed <;> rfl
  have mappedSame : (emitted actual).map eraseOutput = (emitted reference).map eraseOutput := by
    rw [← erasedEmitted actual, ← erasedEmitted reference, erasedSame]
  refine ⟨erasedSame, ?_⟩
  intro output outputMember
  have mappedMember : eraseOutput output ∈ (emitted reference).map eraseOutput := by
    rw [← mappedSame]
    exact List.mem_map.mpr ⟨output, outputMember, rfl⟩
  obtain ⟨referenceOutput, referenceMember, referenceSame⟩ := List.mem_map.mp mappedMember
  have cacheSame : referenceOutput.cache = output.cache :=
    congrArg (fun erased : Output (bits + 2) Unit => erased.cache) referenceSame
  have callerSame : referenceOutput.caller = output.caller :=
    congrArg (fun erased : Output (bits + 2) Unit => erased.caller) referenceSame
  have queriesSame : referenceOutput.queries = output.queries :=
    congrArg (fun erased : Output (bits + 2) Unit => erased.queries) referenceSame
  refine ⟨referenceOutput, referenceMember, referenceSame.symm,
    cacheSame, callerSame, queriesSame, ?_⟩
  intro readFuel actualPartial after program supplied
  rcases supplied with ⟨reading, projection⟩
  refine ⟨?_, projection⟩
  intro extra
  rw [callerSame, cacheSame]
  exact reading extra

end MicroCFTA.SourceSynthesisCurrentInitialIdentityMetadataErasure
