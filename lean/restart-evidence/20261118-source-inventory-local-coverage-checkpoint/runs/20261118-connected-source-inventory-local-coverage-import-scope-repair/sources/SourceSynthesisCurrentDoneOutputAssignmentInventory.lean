import MicroCFTA.SourceSynthesisCurrentDoneAssignment
import MicroCFTA.SourceCurrentClosedRecursiveBoundaryMuOrigin
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive

namespace MicroCFTA.SourceSynthesisCurrentDoneAssignment
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourcePruningEnumerationNodes (lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false

/- Note [One current assignment in both source ownership cases]
The actual accepted source has no Mu or one stored universe owner.
NoNewMu links the same current heap to that source heap.
If the source has no Mu, the done receipt excludes pending native handles.
None-handle slots retain the explicit empty-bucket condition.
The common pending choice and current assignment use the same cache.
This result does not establish residual guards or historical obligations.
-/

theorem actual_done_output_assignment_of_original_source_inventory
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
    (sourceInventory : InternedShallowHeap.NoNewMu
      sourceHeap output.caller.checked.native.machine.heap)
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
  rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
      lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
  · obtain ⟨level, frontier, ordered⟩ := packet.ordered
    apply EnumerationPendingAssignment.stratified_pending_assignment output.cache.core packet.safe
      level frontier ordered (.node (literal "var1") [])
      (handles (SourceEqualityPCSGuard.holds formulas solver) ambient
        output.caller.checked.native.machine.heap)
    intro slot node scs atSlot
    cases node with
    | none =>
        refine ⟨noneBuckets slot scs atSlot, ?_⟩
        intro handle impossible
        cases impossible
    | some handle =>
        obtain ⟨value, _decoded, available, closed, boundary, _emptyBucket⟩ :=
          SourcePruningEnumerationRestart.done_pending_boundary
            order metadata output.caller output.cache packet.valid done slot handle scs atSlot
        obtain ⟨key, entry, body, depth, ordinary, stored⟩ :=
          SourceCurrentClosedRecursiveBoundaryMuOrigin.closed_recursive_boundary_has_source_mu
            sourceHeap output.caller.checked.native.machine.heap normal irreducible
            sourceInventory value available closed boundary
        exact False.elim (noMu key entry body depth ordinary stored)
  · obtain ⟨entry, body, depth, ordinary, stored, _available, _closed, _replay, _unique⟩ := someMu
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
        (muKey depth ordinary) entry body depth ordinary stored
        output.caller.checked.native.machine.heap normal.facts.coherent sourceInventory value available closed
    exact done_current_assignment formulas solver ambient
      lib query signed whole accepted rootValue sourceHeap built
      (muKey depth ordinary) entry body depth ordinary stored
      order metadata inventory output.caller memos output.cache packet done irreducible sourceGrowth
      onlyU noneBuckets

end MicroCFTA.SourceSynthesisCurrentDoneAssignment
