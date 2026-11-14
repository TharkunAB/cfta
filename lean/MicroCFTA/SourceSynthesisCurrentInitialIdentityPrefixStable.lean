import MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefix
import MicroCFTA.SourcePruningEnumerationInitialPrefixFuel

set_option autoImplicit false

/-!
# Positive-fuel identity prefix from one current source initializer

The same successful raw build supplies the root, caller, cache and query memos.
The first decision is retained beside the computed identity prefix.
The read and check use one arbitrary positive fuel budget.
A recursive boundary does not enter that prefix.
This result does not execute preprocessing or the recursive eager worker.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefixStable
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
theorem accepted_initial_identity_prefix_stable
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
            uv = 0 ∧ MergedOrdinaryHeight.recursiveBoundary value = false) := by
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
      closed, original, valueFields, handle, encoded, decoded, slots,
      decision, emptyCase, nonemptyCase, chosen⟩ :=
    SourceSynthesisCurrentInitialIdentityPrefix.accepted_initial_identity_prefix
      lib query signed expression returned depth formulas solver
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
    closed, original, valueFields, handle, encoded, decoded, slots, decision, ?_, ?_, chosen⟩
  · intro emptyValue graph extra nativeFuel representativeFuel indexFuel callbackFuel
    rw [SourcePruningEnumerationSelectedStep.runPrefix_initial_read_check_fuel]
    exact emptyCase emptyValue graph nativeFuel representativeFuel indexFuel callbackFuel
  · intro nonempty graph extra nativeFuel representativeFuel indexFuel callbackFuel
    rw [SourcePruningEnumerationSelectedStep.runPrefix_initial_read_check_fuel]
    exact nonemptyCase nonempty graph nativeFuel representativeFuel indexFuel callbackFuel

end MicroCFTA.SourceSynthesisCurrentInitialIdentityPrefixStable
