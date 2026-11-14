import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisCurrentUniverseGeneratedTypeClosure
import MicroCFTA.SourceRecursiveIntersectionNativeApi

/-!
# Actual cold native requests on two current component Type fields

The same source build supplies both actual first-slot operands.
Their availability, closedness, guard origin and original-U atoms are derived.
Actual native completion and its bounds derive exact kernel correspondence.
Generated-Type closure then applies at that same native result and machine.
This does not prove that a root worker reaches the request.
-/
namespace MicroCFTA.SourceSynthesisCurrentComponentFieldNativeAtoms
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedBinderProtocol (NodeKey)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisOriginalTypeAnnotations (OriginalType)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisPr210TypeReflection (encodeTy)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Actual component slots supply all operand certificates for this completed cold native request. -/
theorem current_component_fields_cold_native_result_atoms
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    {leftExpressions rightExpressions : List (EdgeSyntax Symbol Guard)}
    {leftBefore leftAfter rightBefore rightAfter : State Symbol Guard}
    {leftOutputs rightOutputs : List (EdgeValue Symbol Guard)}
    {leftIndex rightIndex : Nat} {leftSymbol rightSymbol : Symbol}
    (leftScheme rightScheme : Ty) (leftOriginal : OriginalType lib leftScheme)
    (rightOriginal : OriginalType lib rightScheme)
    (leftCall : RowCall leftExpressions [] leftBefore leftOutputs leftAfter sourceHeap leftIndex leftSymbol top
      [ordinarySymbols (generalize
        (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) (encodeTy leftScheme))])
    (rightCall : RowCall rightExpressions [] rightBefore rightOutputs rightAfter sourceHeap rightIndex rightSymbol top
      [ordinarySymbols (generalize
        (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) (encodeTy rightScheme))])
    (left right : Value Symbol Guard)
    (leftSlot : leftCall.output.children[0]? = some left)
    (rightSlot : rightCall.output.children[0]? = some right) (width : Nat) :
    let machine : Machine Symbol Guard := ⟨sourceHeap, Cache.emptyState⟩
    let before := SourceRecursiveIntersectionThunks.initial width machine
    let request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard :=
      ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    ∀ (nativeFuel : Nat) (value : Value Symbol Guard)
      (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (actual : SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin nativeFuel
        (.node request .pure) before = .done value after),
      SourceRecursiveIntersectionNative.Bounds
        (SourceRecursiveIntersectionNative.evaluation_of_done top SourceEqualityPCSNativeEdge.conjoin nativeFuel
          (.node request .pure) before after value actual) →
      (Available sourceHeap left ∧ left.free = [] ∧ Annotated (Origin (encodedLibrary lib)) left ∧
        ∀ atom ∈ atoms left, atom = .mu entry.identity) ∧
      (Available sourceHeap right ∧ right.free = [] ∧ Annotated (Origin (encodedLibrary lib)) right ∧
        ∀ atom ∈ atoms right, atom = .mu entry.identity) ∧
      SourceRecursiveIntersectionThunks.Valid width top SourceEqualityPCSNativeEdge.conjoin after ∧
      Extension machine after.machine ∧ Available after.machine.heap value ∧ value.free = [] ∧
        ∀ atom ∈ atoms value, atom = .mu entry.identity := by
  let machine : Machine Symbol Guard := ⟨sourceHeap, Cache.emptyState⟩
  let before := SourceRecursiveIntersectionThunks.initial width machine
  let request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard :=
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  dsimp only
  intro nativeFuel value after actual ranges
  have leftFacts : Available sourceHeap left ∧ left.free = [] ∧ Annotated (Origin (encodedLibrary lib)) left := by
    obtain ⟨sourceValue, selected, available, closed, typed⟩ :=
      SourceSynthesisCurrentTypeFieldCalls.component_call lib query signed whole accepted rootValue sourceHeap built
        leftScheme leftOriginal leftCall
    have same : sourceValue = left := Option.some.inj (selected.symm.trans leftSlot)
    exact same ▸ ⟨available, closed, typed⟩
  have rightFacts : Available sourceHeap right ∧ right.free = [] ∧ Annotated (Origin (encodedLibrary lib)) right := by
    obtain ⟨sourceValue, selected, available, closed, typed⟩ :=
      SourceSynthesisCurrentTypeFieldCalls.component_call lib query signed whole accepted rootValue sourceHeap built
        rightScheme rightOriginal rightCall
    have same : sourceValue = right := Option.some.inj (selected.symm.trans rightSlot)
    exact same ▸ ⟨available, closed, typed⟩
  have leftAtoms := SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    left leftFacts.1 leftFacts.2.1
  have rightAtoms := SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    right rightFacts.1 rightFacts.2.1
  have constructed := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro item member; cases member)
  have facts : Facts sourceHeap := by
    simpa only [built, Outcome.state] using constructed.facts
  have machineValid : SourceRecursiveIntersectionKernel.Valid machine := ⟨facts, Cache.empty_valid⟩
  have nativeValid := SourceRecursiveIntersectionThunks.initial_valid width top SourceEqualityPCSNativeEdge.conjoin
    machine machineValid
  have requestReady : SourceRecursiveIntersectionThunks.NodeReady machine request :=
    ⟨empty_domain machine, leftFacts.1, rightFacts.1⟩
  obtain ⟨afterValid, extension, _nativeAvailable, bound, exactKernel⟩ :=
    SourceRecursiveIntersectionNative.native_node_correct top SourceEqualityPCSNativeEdge.conjoin nativeFuel
      request before after value nativeValid requestReady actual ranges
  have closed :=
    (SourceSynthesisCurrentUniverseGeneratedTypeClosure.current_stored_universe_coupled_fuel_atoms
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored bound).1
      sourceHeap facts (grows_refl sourceHeap) Cache.emptyState Cache.empty_valid left right
      leftFacts.1 rightFacts.1 leftFacts.2.1 rightFacts.2.1 leftAtoms rightAtoms
  have actualKernel : execute top SourceEqualityPCSNativeEdge.conjoin bound IntersectionEmptyDomain.emptyDomain
      left right machine = .done value after.machine := by
    simpa only [request, before, SourceRecursiveIntersectionThunks.initial, Nat.add_zero] using exactKernel 0
  have returned := closed.result value after.machine actualKernel
  exact ⟨⟨leftFacts.1, leftFacts.2.1, leftFacts.2.2, leftAtoms⟩,
    ⟨rightFacts.1, rightFacts.2.1, rightFacts.2.2, rightAtoms⟩,
    afterValid, extension, returned.1, returned.2.1, returned.2.2⟩

end MicroCFTA.SourceSynthesisCurrentComponentFieldNativeAtoms
