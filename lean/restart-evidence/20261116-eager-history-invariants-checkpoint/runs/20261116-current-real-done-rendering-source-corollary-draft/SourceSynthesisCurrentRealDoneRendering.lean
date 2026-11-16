import MicroCFTA.SourceSynthesisCurrentRealDoneAssignmentNoneBuckets
import MicroCFTA.SourceSynthesisCurrentDoneRendering

namespace MicroCFTA.SourceSynthesisCurrentRealDoneRendering
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

theorem accepted_real_rendered_assignment
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
          ∀ (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
            (body muDepth ordinary : Node),
            sourceHeap.nodeRecords key = some (.mu entry body muDepth ordinary) →
            (∀ (slot handle : Nat) (scs : List EnumerationState.Suspended),
              output.cache.core.values[slot]? = some (.unenumerated (some handle) scs) →
              ∀ value, lookupNode output.caller.checked.native.machine.heap handle = some value →
              ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) →
            ∀ (renderFuel uv : Nat) (after : EnumerationState.State Symbol Guard)
              (term : Term Symbol) (pending : List (Guard × Term Symbol)),
              EnumerationCorrectness.Success
                (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap
                  (literal "var1") renderFuel uv) output.cache.core (term, pending) after →
              (∀ obligation ∈ pending,
                SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
              ∃ assignment : Nat → Term Symbol,
                EnumerationCorrectness.Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles
                    (SourceEqualityPCSGuard.holds formulas solver) ambient
                    output.caller.checked.native.machine.heap)
                  (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
                  assignment output.cache.core ∧
                term = assignment uv ∧ EnumerationCompressionFrame.Frame output.cache.core after ∧
                EnumerationCorrectness.Satisfies
                  (SourcePruningEnumerationNativeLanguage.handles
                    (SourceEqualityPCSGuard.holds formulas solver) ambient
                    output.caller.checked.native.machine.heap)
                  (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
                  assignment after ∧
                (∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                  (readAfter : EnumerationState.State Symbol Guard),
                  EnumerationCorrectness.Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap readFuel)
                    output.cache.core actualPartial readAfter →
                  SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
                ∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                  (readAfter : EnumerationState.State Symbol Guard),
                  EnumerationCorrectness.Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap readFuel) after actualPartial readAfter →
                  SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)
 := by
  dsimp only
  obtain ⟨fields, cache, rootValue, sourceHeap, built, allocation, context, facts, available, closed,
      handle, encoded, decoded, previousOutputs⟩ :=
    SourceSynthesisCurrentRealDoneAssignmentNoneBuckets.accepted_real_done_assignment
      lib query signed expression accepted workFuel depth formulas solver ambient metadata emptyPending
      holeKey fits admits graph templates checkEmpty order
  refine ⟨fields, cache, rootValue, sourceHeap, built, allocation, context, facts, available, closed,
    handle, encoded, decoded, ?_⟩
  intro output member
  obtain ⟨resources, noMetadata, defaultDone, normal, unionNormal, growth, noneBuckets, _models⟩ :=
    previousOutputs output member
  refine ⟨resources, noMetadata, defaultDone, normal, unionNormal, growth, noneBuckets, ?_⟩
  intro key entry body muDepth ordinary stored onlyU renderFuel uv after term pending observed checked
  obtain ⟨inventory, final, nextMetadata, _post, _querySame, packet, _metadataShape,
      _outputFits, _outputHeap⟩ := resources
  have done : SourcePruningEnumerationRestart.decision none (fun _ _ => none)
      nextMetadata output.cache = some .done := by
    change some (EnumerationPureSelection.next (fun _ => none) output.cache) = some .done
    rw [defaultDone]
  obtain ⟨assignment, current, rendered, frame, afterCurrent⟩ :=
    SourceSynthesisCurrentDoneRendering.rendered_current_assignment
      formulas solver ambient lib query signed expression accepted rootValue sourceHeap built
      key entry body muDepth ordinary stored (fun _ _ => none) nextMetadata
      inventory output.caller final output.cache packet done unionNormal growth onlyU noneBuckets
      renderFuel uv after term pending observed checked
  have partials (state : EnumerationState.State Symbol Guard)
      (total : UnionFind.Total state.representatives)
      (satisfied : EnumerationCorrectness.Satisfies
        (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient
          output.caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment state) :
      ∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
        (readAfter : EnumerationState.State Symbol Guard),
        EnumerationCorrectness.Success (SourcePruningEnumerationPartialOutput.rootPartial
          output.caller.checked.native.machine.heap readFuel) state actualPartial readAfter →
        SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0) := by
    have equations : SourcePruningPartialRenderingSemantics.StoredEquations assignment state := by
      refine ⟨satisfied.1.1, ?_⟩
      intro slot fragment present
      simpa only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot,
        Fragments.slotSatisfies] using satisfied.1.2 slot
    intro readFuel actualPartial readAfter actual
    exact SourcePruningEnumerationPartialOutput.rootPartial_completes_of_stored_equations
      output.caller.checked.native.machine.heap assignment readFuel state readAfter actualPartial
      total equations actual
  exact ⟨assignment, current, rendered, frame, afterCurrent,
    partials output.cache.core packet.safe.1.total current,
    partials after (frame.total packet.safe.1.total) afterCurrent⟩

end MicroCFTA.SourceSynthesisCurrentRealDoneRendering
