import MicroCFTA.SourceSynthesisCurrentProgramEagerResources
import MicroCFTA.SourceSynthesisCurrentDoneAssignment
import MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormalWhole
import MicroCFTA.SourcePruningEnumerationPartialOutput

namespace MicroCFTA.SourceSynthesisCurrentRealDoneAssignment
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceEqualityConstraintOrigins (guards)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationSharedPreparedRecursive (OutputResources emitted)
open SourceSynthesisOriginalSharedRankCompletion (seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false
variable {Typing Key : Type}
variable [DecidableEq FullSyntax.Formula] [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem accepted_real_done_assignment
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (workFuel depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (order : Metadata Typing → List Nat → Option Nat) :
    let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
    ∃ fields cache rootValue sourceHeap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty =
        InternedNestedConstruction.Outcome.done rootValue sourceHeap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      SourceCurrentAllocatedPartialInvariant.Context formulas solver
        (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) rootValue sourceHeap built)
        (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache sourceHeap)
        SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts sourceHeap ∧ Available sourceHeap rootValue ∧ rootValue.free = [] ∧
      ∃ handle, encodeNode rootValue = some handle ∧ lookupNode sourceHeap handle = some rootValue ∧
        let startup : Cached :=
          ⟨EnumerationState.initial handle,
            fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
            fun _ => none⟩
        let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache sourceHeap
        let outcome := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
          (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty InternedEdgeResidency.nodeEdges none order workFuel depth metadata
          initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup
        ∀ output ∈ emitted outcome,
          OutputResources formulas solver initialCaller
            (SourcePruningEnumerationSharedEagerReservation.eagerFinal depth (seed sourceHeap) 0) output ∧
          output.metadata = none ∧ EnumerationPureSelection.next (fun _ => none) output.cache = .done ∧
          InternedStoredMuOrigins.Normal output.caller.checked.native.machine.heap ∧
          SourceCurrentRequiredUnionNormal.UnionNormal output.caller.checked.native.machine.heap ∧
          Grows sourceHeap output.caller.checked.native.machine.heap ∧
          ∀ (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
            (body muDepth ordinary : Node),
            sourceHeap.nodeRecords key = some (.mu entry body muDepth ordinary) →
            (∀ (slot handle : Nat) (scs : List EnumerationState.Suspended),
              output.cache.core.values[slot]? = some (.unenumerated (some handle) scs) →
              ∀ value, lookupNode output.caller.checked.native.machine.heap handle = some value →
              ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) →
            (∀ (slot : Nat) (scs : List EnumerationState.Suspended),
              output.cache.core.values[slot]? = some (.unenumerated none scs) → scs = []) →
            ∃ assignment : Nat → Term Symbol,
              Fragments.stateSatisfies output.cache.core.representatives
                (EnumerationCorrectness.heap
                  (SourcePruningEnumerationNativeLanguage.handles
                    (SourceEqualityPCSGuard.holds formulas solver) ambient
                    output.caller.checked.native.machine.heap)
                  output.cache.core.values) assignment ∧
              (∀ (slot : Nat) (node : Option Nat) (scs : List EnumerationState.Suspended),
                output.cache.core.values[slot]? = some (.unenumerated node scs) →
                assignment slot = .node (literal "var1") []) ∧
              ∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                (after : EnumerationState.State Symbol Guard),
                EnumerationCorrectness.Success (SourcePruningEnumerationPartialOutput.rootPartial
                  output.caller.checked.native.machine.heap readFuel) output.cache.core actualPartial after →
                SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)
 := by
  dsimp only
  let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
  obtain ⟨fields, cache, rootValue, sourceHeap, built, allocation, _conjunctionFields, context,
      facts, available, _roles, _growth, _issued, _origins, _identity, _emptySame, _emptyReady,
      closed, _original, _valueFields, handle, encoded, decoded, _slots⟩ :=
    SourceSynthesisCurrentProgramSlotsInitialization.accepted lib query signed expression accepted
      (bits + 2) Cache.emptyState Cache.empty_valid formulas solver
  let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache sourceHeap
  let initialInventory :=
    SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) rootValue sourceHeap built
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
      fun _ => none⟩
  obtain ⟨initialHandle, initialEncoded, _initialDecoded, startupReceipt⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_carriers formulas solver initialInventory
      initialCaller SourceCurrentAllocatedPartialInitialization.globals metadata rootValue
      context available closed emptyPending
  have handleSame : initialHandle = handle := Option.some.inj (initialEncoded.symm.trans encoded)
  subst initialHandle
  have initialFits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits
      (seed sourceHeap).2 initialCaller.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial sourceHeap facts⟩
  have initialHeap : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed sourceHeap).1) sourceHeap :=
    SourceCurrentConjunctionGuardUniverse.initial sourceHeap facts
  have reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits depth (seed sourceHeap) 0 :=
    SourceSynthesisCurrentProgramEagerEnumerationWidth.eager_reserved_of_build
      lib query signed expression accepted depth rootValue sourceHeap built
  have resources := SourcePruningEnumerationSharedEagerReservation.runEager_real_emitted_complete_resources_at_any_budget
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
    formulas solver depth initialInventory initialCaller SourceCurrentAllocatedPartialInitialization.globals
    startup metadata (seed sourceHeap) 0 startupReceipt.1.1 initialFits initialHeap
    (fun _ _ _ _ _ member => member) (fun _ _ _ _ => Nat.le_refl _)
    (Nat.le_of_eq startupReceipt.1.2.2.2.1) reserved workFuel
  have initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal sourceHeap := by
    have sourceNormal := SourceCurrentRequiredUnionNormal.source (ordinarySymbols expression)
    rw [built] at sourceNormal
    exact sourceNormal
  have normalRun := SourcePruningEnumerationSharedEagerUnionNormal.runEager_real_unionNormal_at_any_budget
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
    workFuel depth metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup initialNormal
  dsimp only at normalRun
  have outputsNormal : ∀ output ∈ emitted
      (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty InternedEdgeResidency.nodeEdges none order workFuel depth metadata
        initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup),
      SourceCurrentRequiredUnionNormal.UnionNormal output.caller.checked.native.machine.heap := by
    cases observed : SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty InternedEdgeResidency.nodeEdges none order workFuel depth metadata
        initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup with
    | complete outputs reached saved =>
        rw [observed] at normalRun
        exact normalRun.1
    | stopped outputs reason reached =>
        rw [observed] at normalRun
        exact normalRun.1
  refine ⟨fields, cache, rootValue, sourceHeap, built, allocation, context, facts, available, closed,
    handle, encoded, decoded, ?_⟩
  intro output member
  have outputResources := resources.1 output member
  obtain ⟨next, final, outputMetadata, post, _querySame, packet, _metadataShape,
      _outputFits, _outputHeap⟩ := outputResources
  have outputNormal := packet.context.ready.semantic.ready.semantic.1.normal
  have outputGrowth : Grows sourceHeap output.caller.checked.native.machine.heap := post.effects.keeps.growth
  have controlled := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager_output_control
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
    workFuel depth metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup
    output member
  have noMetadata := controlled.2 rfl
  have defaultDone := controlled.1 noMetadata
  have irreducible := outputsNormal output member
  refine ⟨outputResources, noMetadata, defaultDone, outputNormal, irreducible, outputGrowth, ?_⟩
  intro key entry body muDepth ordinary stored onlyU noneBuckets
  have done : SourcePruningEnumerationRestart.decision none (fun _ _ => none)
      outputMetadata output.cache = some .done := by
    change some (EnumerationPureSelection.next (fun _ => none) output.cache) = some .done
    rw [defaultDone]
  obtain ⟨assignment, current, pending⟩ := SourceSynthesisCurrentDoneAssignment.done_current_assignment
    formulas solver ambient lib query signed expression accepted rootValue sourceHeap built
    key entry body muDepth ordinary stored (fun _ _ => none) outputMetadata next
    output.caller final output.cache packet done irreducible outputGrowth onlyU noneBuckets
  refine ⟨assignment, current, pending, ?_⟩
  intro readFuel actualPartial after actual
  have equations : SourcePruningPartialRenderingSemantics.StoredEquations assignment output.cache.core := by
    refine ⟨current.1, ?_⟩
    intro slot fragment present
    simpa only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot,
      Fragments.slotSatisfies] using current.2 slot
  exact SourcePruningEnumerationPartialOutput.rootPartial_completes_of_stored_equations
    output.caller.checked.native.machine.heap assignment readFuel output.cache.core after actualPartial
    packet.safe.1.total equations actual

end MicroCFTA.SourceSynthesisCurrentRealDoneAssignment

#check MicroCFTA.SourceSynthesisCurrentRealDoneAssignment.accepted_real_done_assignment
#print axioms MicroCFTA.SourceSynthesisCurrentRealDoneAssignment.accepted_real_done_assignment
