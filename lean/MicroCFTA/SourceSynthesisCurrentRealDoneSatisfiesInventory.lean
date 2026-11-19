import MicroCFTA.SourceSynthesisCurrentRealDoneAssignmentInventory
import MicroCFTA.SourceSynthesisCurrentGuardPoolPositivity

namespace MicroCFTA.SourceSynthesisCurrentRealDoneSatisfiesInventory
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

theorem accepted_real_done_satisfies_from_original_inventory
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
          SourcePruningEnumerationSharedEagerNoneBuckets.NoneBucketsEmpty output.cache.core ∧
            ∃ assignment : Nat → Term Symbol,
              (Fragments.stateSatisfies output.cache.core.representatives
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
                SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
              EnumerationCorrectness.Satisfies
                (SourcePruningEnumerationNativeLanguage.handles
                  (SourceEqualityPCSGuard.holds formulas solver) ambient
                  output.caller.checked.native.machine.heap)
                (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                assignment output.cache.core
 := by
  dsimp only
  let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
  obtain ⟨fields, cache, rootValue, sourceHeap, built, allocation, context, facts, available, closed,
      handle, encoded, decoded, previousOutputs⟩ :=
    SourceSynthesisCurrentRealDoneAssignmentInventory.accepted_real_done_assignment_from_original_inventory
      lib query signed expression accepted workFuel depth formulas solver ambient metadata emptyPending
      holeKey fits admits graph templates checkEmpty order
  let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache sourceHeap
  let initialInventory :=
    SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) rootValue sourceHeap built
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
      fun _ => none⟩
  let outcome := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty InternedEdgeResidency.nodeEdges none order workFuel depth metadata
    initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup
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
  have initialTop : ∀ guard ∈ (seed sourceHeap).1, guard.guard = .top := by
    intro guard member
    exact (SourceSynthesisCurrentGuardPoolPositivity.accepted_source_seed_guard_pool_positive
      lib query signed expression accepted rootValue sourceHeap built 0 guard member).1
  have preserved := SourcePruningEnumerationSharedEagerReservation.runEager_real_preserves_obligations_at_any_budget
    (bits := bits) holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
    formulas solver depth initialInventory initialCaller SourceCurrentAllocatedPartialInitialization.globals
    startup metadata (seed sourceHeap) 0 startupReceipt.1.1 initialFits initialHeap initialTop
    (fun _ _ _ _ _ member => member) (fun _ _ _ _ => Nat.le_refl _)
    (Nat.le_of_eq startupReceipt.1.2.2.2.1) reserved workFuel
  change ∀ output ∈ emitted outcome,
    output.cache.core.obligations = startup.core.obligations at preserved
  have outputLists : ∀ output ∈ emitted outcome, output.cache.core.obligations = [] := by
    intro output member
    exact preserved output member
  refine ⟨fields, cache, rootValue, sourceHeap, built, allocation, context, facts, available, closed,
    handle, encoded, decoded, ?_⟩
  intro output member
  obtain ⟨resources, noMetadata, defaultDone, normal, unionNormal, growth, noneBuckets,
      assignment, current, pending, partialCompletes⟩ := previousOutputs output member
  refine ⟨resources, noMetadata, defaultDone, normal, unionNormal, growth, noneBuckets,
    assignment, ⟨current, pending, partialCompletes⟩, ?_⟩
  refine ⟨current, ?_⟩
  change EnumerationCorrectness.guardsHold
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
    assignment output.cache.core.obligations
  rw [outputLists output member]
  intro obligation listed
  cases listed

end MicroCFTA.SourceSynthesisCurrentRealDoneSatisfiesInventory
