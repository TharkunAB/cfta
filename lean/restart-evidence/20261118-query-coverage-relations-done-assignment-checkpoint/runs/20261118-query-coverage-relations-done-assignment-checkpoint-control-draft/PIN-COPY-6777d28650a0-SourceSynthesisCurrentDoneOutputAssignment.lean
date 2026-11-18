import MicroCFTA.SourceSynthesisCurrentDoneAssignment
import MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive

namespace MicroCFTA.SourceSynthesisCurrentDoneAssignment
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourcePruningEnumerationNodes (lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false

/- Note [One current assignment from the original source inventory]
The pending read and the Seeds inventory use the same output caller.
The actual done boundary supplies closed available values at that caller.
The source inventory derives only-U atoms before the existing assignment proof.
This result does not certify residual guards or historical obligations.
-/

theorem actual_done_output_assignment_of_original_source_seeds
    {Typing : Type} {width : Nat}
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) []
      InternedConstructorTemplates.empty = InternedNestedConstruction.Outcome.done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (memos : EndpointMemoGateTrace.Memos)
    (output : SourcePruningEnumerationSharedPreparedRecursive.Output width Typing)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory
      output.caller memos metadata output.cache)
    (done : SourcePruningEnumerationRestart.decision none order metadata output.cache = some .done)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal output.caller.checked.native.machine.heap)
    (sourceGrowth : Grows sourceHeap output.caller.checked.native.machine.heap)
    (bodyId : Nat)
    (endpointSeeds : SourceCurrentNativeNumericalSeedInvariant.Seeds
      sourceHeap entry body depth ordinary bodyId output.caller.checked)
    (noneBuckets : ∀ (slot : Nat) (scs : List EnumerationState.Suspended),
      output.cache.core.values[slot]? = some (.unenumerated none scs) → scs = []) :
    ∃ assignment : Nat → Term Symbol,
      Fragments.stateSatisfies output.cache.core.representatives
        (EnumerationCorrectness.heap
          (handles (SourceEqualityPCSGuard.holds formulas solver) ambient
            output.caller.checked.native.machine.heap)
          output.cache.core.values) assignment ∧
      ∀ (slot : Nat) (node : Option Nat) (scs : List EnumerationState.Suspended),
        output.cache.core.values[slot]? = some (.unenumerated node scs) →
        assignment slot = .node (literal "var1") []
 := by
  have normal := packet.context.ready.semantic.ready.semantic.1.normal
  have unchanged : InternedShallowHeap.NoNewMu sourceHeap
      output.caller.checked.native.machine.heap := endpointSeeds.1
  have onlyU : ∀ (slot handle : Nat) (scs : List EnumerationState.Suspended),
      output.cache.core.values[slot]? = some (.unenumerated (some handle) scs) →
      ∀ value, lookupNode output.caller.checked.native.machine.heap handle = some value →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity := by
    intro slot handle scs atSlot value decoded
    obtain ⟨actualValue, actualRead, available, closed, _boundary, _emptyBucket⟩ :=
      SourcePruningEnumerationRestart.done_pending_boundary
        order metadata output.caller output.cache packet.valid done slot handle scs atSlot
    have same : actualValue = value := Option.some.inj (actualRead.symm.trans decoded)
    subst actualValue
    exact SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built
      key entry body depth ordinary stored output.caller.checked.native.machine.heap
      normal.facts.coherent unchanged value available closed
  exact done_current_assignment formulas solver ambient
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    order metadata inventory output.caller memos output.cache packet done irreducible sourceGrowth
    onlyU noneBuckets

end MicroCFTA.SourceSynthesisCurrentDoneAssignment

#print axioms MicroCFTA.SourceSynthesisCurrentDoneAssignment.actual_done_output_assignment_of_original_source_seeds
