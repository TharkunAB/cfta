import MicroCFTA.SourceSynthesisCurrentProgramEagerOutputs
import MicroCFTA.SourcePruningEnumerationIdentityPrefix

set_option autoImplicit false

/-!
# Identity prefix from one current source initializer

The same accepted raw build supplies the root, caller, cache and query memos.
The first decision is retained beside the computed identity prefix.
A recursive boundary does not enter that prefix.
This result does not execute preprocessing or the recursive eager worker.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefix
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One accepted raw initializer supplies the exact default decision and identity prefix. -/
theorem accepted_initial_identity_prefix
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
          (value = .empty → ∀ (graph : Graph Symbol Guard) nativeFuel representativeFuel indexFuel callbackFuel,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow (fun _ _ _ node state => .done node state)
              graph [] none (fun _ _ => none) metadata 1 1 nativeFuel representativeFuel indexFuel callbackFuel
              0 caller startup SourceCurrentAllocatedPartialInitialization.globals.query =
            .narrowed (EnumerationState.initial handle)
              (.done (value, some (EnumerationState.reject : EnumerationState.EnumerateM Symbol Guard Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
                caller.fourth caller.merge)
              SourceCurrentAllocatedPartialInitialization.globals.query (some []) none none none) ∧
          (value ≠ .empty → ∀ (graph : Graph Symbol Guard) nativeFuel representativeFuel indexFuel callbackFuel,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow (fun _ _ _ node state => .done node state)
              graph [] none (fun _ _ => none) metadata 1 1 nativeFuel representativeFuel indexFuel callbackFuel
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
            uv = 0 ∧ MergedOrdinaryHeight.recursiveBoundary value = false) := by
  classical
  let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
      closed, original, valueFields, handle, encoded, decoded, slots⟩ :=
    SourceSynthesisCurrentProgramSlotsInitialization.accepted lib query signed expression returned
      (bits + 2) Cache.emptyState Cache.empty_valid formulas solver
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
    closed, original, valueFields, handle, encoded, decoded, slots, ?_⟩
  let caller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
  let core : Core := EnumerationState.initial handle
  let startup : Cached :=
    ⟨core, fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
      fun _ => none⟩
  let metadata : Metadata Unit := ⟨[], [], [], ()⟩
  have ready : SourceEqualityRequiredCache.Ready heap :=
    SourceEqualityRequiredCache.constructed (ordinarySymbols expression) value heap built
  have realized : SourcePruningEnumerationObservation.PendingRealized heap core := by
    obtain ⟨found, foundEncoded, foundRealized⟩ :=
      SourcePruningEnumerationObservation.initial_realized (EnumGuard := Guard)
        heap value facts.coherent available closed
    have same : found = handle := Option.some.inj (foundEncoded.symm.trans encoded)
    subst found
    exact foundRealized
  have reading : ExceptT.run (EnumerationState.getValue 1 0 core) =
      [.ok (.unenumerated (some handle) [], core)] := by rfl
  have checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap 1 0 handle [] core) =
      [.ok (false, core)] := by
    cases boundary : MergedOrdinaryHeight.recursiveBoundary value <;>
      simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
        EnumerationState.representative, core, EnumerationState.initial,
        UnionFind.findRoot, UnionFind.withInitialValues]
  have prefix (graph : Graph Symbol Guard) :=
    SourcePruningEnumerationSelectedStep.runPrefix_identity_pending graph [] none
      (fun _ _ => none) metadata caller startup SourceCurrentAllocatedPartialInitialization.globals.query
      1 1 0 handle [] core core ready realized (UnionFind.initial_total [0])
      reading checking (EnumerationCompressionFrame.Frame.refl core)
  have decision : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup =
      some (if MergedOrdinaryHeight.recursiveBoundary value then .done else .expand 0) := by
    cases boundary : MergedOrdinaryHeight.recursiveBoundary value <;>
      simp [SourcePruningEnumerationRestart.decision, EnumerationPureSelection.next,
        EnumerationPureSelection.find, EnumerationIndexSelection.candidates,
        EnumerationState.pickNext, startup, core, EnumerationState.initial, boundary]
  refine ⟨decision, ?_, ?_, ?_⟩
  · intro emptyValue graph nativeFuel representativeFuel indexFuel callbackFuel
    obtain ⟨found, foundDecoded, _encoded, _available, _closed, emptyCase, _nonemptyCase⟩ := prefix graph
    have same : found = value := Option.some.inj (foundDecoded.symm.trans decoded)
    subst found
    exact emptyCase emptyValue nativeFuel representativeFuel indexFuel callbackFuel
  · intro nonempty graph nativeFuel representativeFuel indexFuel callbackFuel
    obtain ⟨found, foundDecoded, _encoded, _available, _closed, _emptyCase, nonemptyCase⟩ := prefix graph
    have same : found = value := Option.some.inj (foundDecoded.symm.trans decoded)
    subst found
    exact nonemptyCase nonempty nativeFuel representativeFuel indexFuel callbackFuel
  · intro uv chosen
    rw [decision] at chosen
    cases boundary : MergedOrdinaryHeight.recursiveBoundary value with
    | false =>
        have zero : 0 = uv := by simpa [boundary] using chosen
        exact ⟨zero.symm, boundary⟩
    | true => simp [boundary] at chosen

end MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefix

#print axioms MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefix.accepted_initial_identity_prefix
