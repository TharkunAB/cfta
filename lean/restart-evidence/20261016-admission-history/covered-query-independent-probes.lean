import MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery


-- AdmissionExecution public axiom reports.
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.body_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.step_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.execute_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.done_admitted

-- AdmissionExecution complete public signatures.
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.RequestCovered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.RequestsThrough
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.body_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.step_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.execute_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution.done_admitted

-- AdmissionCode public axiom reports.
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.certified_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.requestEdge_certified
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.walk_certified

-- AdmissionCode complete public signatures.
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.Certified
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.certified_bind
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.requestEdge_certified
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode.walk_certified

-- AdmissionTrace public axiom reports.
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.current
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.yielded_certified
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered

-- AdmissionTrace complete public signatures.
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.Branches
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.ControlCertified
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.current
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.yielded_certified
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered

-- CoveredQuery public axiom reports.
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.branches
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.query_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.generated_complete

-- CoveredQuery complete public signatures.
#check MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.Receipt
#check MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.branches
#check MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.query_complete
#check MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery.generated_complete

namespace MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeAdmissionCache SourceCurrentAllocatedNativeCoveredQuery
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Execution integration 1: every finite outcome retains both weaker invariants.
theorem execution_all_outcomes {semanticView : View Symbol} (inputs : FiniteInput semanticView)
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (covered : Covered inputs state.native)
    (requests : SourceCurrentAllocatedNativeAdmissionExecution.RequestsThrough inputs fuel control state) :
    SourceCurrentAllocatedNativeInputModelTransport.Admitted semanticView (finiteInputMeaning semanticView inputs)
      (execute fuel control state).state.native ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs (execute fuel control state).state.native := by
  have retained := SourceCurrentAllocatedNativeAdmissionExecution.execute_covered inputs fuel control state covered requests
  exact ⟨retained.admitted, retained.seen_admitted⟩

-- Execution integration 2: a literal done identifies the same complete final checked state.
theorem execution_done_full_state {semanticView : View Symbol} (inputs : FiniteInput semanticView)
    (fuel : Nat) (control : Control Output) (before after : Checked width) (value : Output)
    (covered : Covered inputs before.native)
    (requests : SourceCurrentAllocatedNativeAdmissionExecution.RequestsThrough inputs fuel control before)
    (done : execute fuel control before = .done value after) :
    Covered inputs after.native ∧
    SourceCurrentAllocatedNativeInputModelTransport.Admitted semanticView (finiteInputMeaning semanticView inputs) after.native ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs after.native :=
  SourceCurrentAllocatedNativeAdmissionExecution.done_admitted inputs fuel control before after value covered requests done

section Static
variable (source : State Symbol Guard) (holds : Guard → Term Symbol → Bool)
  (inputs : FiniteInput (view source holds))

omit [DecidableEq Symbol] in
-- Code integration 1: request admission is derived before execution or publication.
theorem node_admission_before_publication (request : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (scope : NodeScope source request) (known : NodeCovered inputs request) :
    SourceCurrentAllocatedNativeAdmissionExecution.RequestCovered inputs
      (.code (requestNode request.domain request.left request.right)) :=
  SourceCurrentAllocatedNativeAdmissionTrace.current source holds inputs _ machine
    (fun after value => Available after.heap value)
    (SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs request machine scope known)

omit [DecidableEq Symbol] in
-- Code integration 2: an ordered request list needs local input coverage, not completed calls.
theorem ordered_node_requests (requests : List (NodeRequest Symbol Guard)) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (semantic : SemanticReady machine.heap)
    (known : ∀ request ∈ requests, NodeScope source request ∧ NodeCovered inputs request) :
    SourceCurrentAllocatedNativeAdmissionCode.Certified source holds inputs
      (walk (fun request => requestNode request.domain request.left request.right) requests) machine
      (fun after values => ∀ value ∈ values, Available after.heap value) := by
  apply SourceCurrentAllocatedNativeAdmissionCode.walk_certified source holds inputs _ requests
    (fun _ request => NodeScope source request ∧ NodeCovered inputs request)
    (fun after value => Available after.heap value)
    (fun _ _ _ _ input => input) available_stable _ machine valid semantic known
  intro request _ current _ _ admitted
  exact SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs
    request current admitted.1 admitted.2

-- Trace integration: a concrete branch family derives all final admission from an actual physical trace.
theorem concrete_trace_admission (facts : InternedNestedFacts.Facts source) {A : Type}
    {fuel : Nat} {control next : Control A} {before after : Checked width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before next after)
    (post : Machine Symbol Guard → A → Prop) (good : Good before)
    (semantic : SemanticReady before.native.machine.heap)
    (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (covered : Covered inputs before.native)
    (certificate : SourceCurrentAllocatedNativeAdmissionTrace.ControlCertified
      source holds inputs control before.native.machine post) :
    Covered inputs after.native ∧
    SourceCurrentAllocatedNativeInputModelTransport.Admitted (view source holds)
      (finiteInputMeaning (view source holds) inputs) after.native ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs after.native := by
  have retained := SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered source holds inputs
    (branches source facts holds inputs) trace post good semantic growth history fields covered certificate
  exact ⟨retained.1, retained.1.admitted, retained.1.seen_admitted⟩
end Static

section Fixed
variable (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
  (state : Checked width) (good : Good state)
  (contextual : SourceCurrentAllocatedNativeContextCache.Contextual (view source (SourceEqualityPCSGuard.holds formulas solver))
    (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs) (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs) (SourceEqualityPCSGuard.holds formulas solver) state.native)
  (covered : Covered inputs state.native)
  (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
  (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
  (growth : Grows source state.native.machine.heap)
  (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
  (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
  (leftAvailable : Available source left) (rightAvailable : Available source right)
  (leftClosed : left.free = []) (rightClosed : right.free = [])
  (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right))
  (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state)
include facts good contextual covered scopedCache semantic idle growth history leftOriginal rightOriginal
  leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges

-- Covered query integration 1: no future request coverage or desired output law is supplied.
theorem fixed_query_exact_and_covered : ∃ fuel value after,
    execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
    value.free = [] ∧ Available after.native.machine.heap value ∧
    Covered inputs after.native ∧
    SourceCurrentAllocatedNativeInputModelTransport.Admitted (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs) after.native ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs after.native ∧
    ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨fuel, value, after, receipt⟩ := query_complete source facts formulas solver inputs state good
    contextual covered scopedCache semantic idle growth history left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges
  exact ⟨fuel, value, after, receipt.toWarmReceipt.done, receipt.closed, receipt.result,
    receipt.covered, receipt.covered.admitted, receipt.covered.seen_admitted, receipt.meaning⟩
end Fixed

section Generated
variable (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
  (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
variable (state : Checked width) (good : Good state)
  (contextual : SourceCurrentAllocatedNativeContextCache.Contextual (view source (SourceEqualityPCSGuard.holds formulas solver))
    (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts (SourceEqualityPCSGuard.holds formulas solver) roots originals available closed)) (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts (SourceEqualityPCSGuard.holds formulas solver) roots originals available closed)) (SourceEqualityPCSGuard.holds formulas solver) state.native)
  (covered : Covered (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts (SourceEqualityPCSGuard.holds formulas solver) roots originals available closed) state.native)
  (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
  (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
  (growth : Grows source state.native.machine.heap)
  (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
  (left right : Value Symbol Guard)
  (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
  (leftClosed : left.free = []) (rightClosed : right.free = [])
  (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state)
include facts originals available closed contextual covered scopedCache semantic idle growth history leftAvailable rightAvailable leftClosed rightClosed ranges

-- Covered query integration 2: exact current inventory witnesses remain available for a later call.
theorem generated_inventory_retained : ∃ targetAvailable : Values state.native.machine.heap (roots ++ [left, right]),
    ∃ targetClosed : ∀ root ∈ (roots ++ [left, right]), root.free = [],
      ∃ fuel value after, Receipt state.native.machine.heap formulas solver (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput state.native.machine.heap good.native.machine.1 (SourceEqualityPCSGuard.holds formulas solver) (roots ++ [left, right])
          (SourceCurrentAllocatedNativeGrownInventory.closed_originals state.native.machine.heap good.native.machine.1 (roots ++ [left, right]) targetAvailable targetClosed) targetAvailable targetClosed)
        fuel left right state value after ∧
        Covered (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput state.native.machine.heap good.native.machine.1 (SourceEqualityPCSGuard.holds formulas solver) (roots ++ [left, right])
          (SourceCurrentAllocatedNativeGrownInventory.closed_originals state.native.machine.heap good.native.machine.1 (roots ++ [left, right]) targetAvailable targetClosed) targetAvailable targetClosed) after.native := by
  obtain ⟨targetAvailable, targetClosed, fuel, value, after, receipt⟩ := generated_complete
    source facts formulas solver roots originals available closed state good contextual covered scopedCache
    semantic idle growth history left right leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨targetAvailable, targetClosed, fuel, value, after, receipt, receipt.covered⟩

-- Covered query integration 3: the first actual output becomes an input to a second generated query.
-- Only the second call's reached word ranges are needed after the first receipt.
theorem two_generated_queries : ∃ firstAvailable : Values state.native.machine.heap (roots ++ [left, right]),
    ∃ firstClosed : ∀ root ∈ (roots ++ [left, right]), root.free = [],
      ∃ firstFuel firstValue firstAfter, ∃ firstGood : Good firstAfter,
        Receipt state.native.machine.heap formulas solver (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput state.native.machine.heap good.native.machine.1 (SourceEqualityPCSGuard.holds formulas solver) (roots ++ [left, right])
          (SourceCurrentAllocatedNativeGrownInventory.closed_originals state.native.machine.heap good.native.machine.1 (roots ++ [left, right]) firstAvailable firstClosed) firstAvailable firstClosed)
          firstFuel left right state firstValue firstAfter ∧
        ∀ _nextRanges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain firstValue right)) firstAfter,
        ∃ secondAvailable : Values firstAfter.native.machine.heap ((roots ++ [left, right]) ++ [firstValue, right]),
          ∃ secondClosed : ∀ root ∈ (roots ++ [left, right]) ++ [firstValue, right], root.free = [],
            let nextInputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
              firstAfter.native.machine.heap
              firstGood.native.machine.1
              (SourceEqualityPCSGuard.holds formulas solver) ((roots ++ [left, right]) ++ [firstValue, right])
              (SourceCurrentAllocatedNativeGrownInventory.closed_originals firstAfter.native.machine.heap
                firstGood.native.machine.1 ((roots ++ [left, right]) ++ [firstValue, right]) secondAvailable secondClosed)
              secondAvailable secondClosed
            ∃ secondFuel secondValue secondAfter,
              execute (secondFuel + 1)
                (.code (requestNode IntersectionEmptyDomain.emptyDomain firstValue right)) firstAfter = .done secondValue secondAfter ∧
              secondValue.free = [] ∧ Available secondAfter.native.machine.heap secondValue ∧
              Covered nextInputs secondAfter.native ∧
              SourceCurrentAllocatedNativeInputModelTransport.Admitted
                (view firstAfter.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver))
                (finiteInputMeaning (view firstAfter.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)) nextInputs) secondAfter.native ∧
              SourceCurrentAllocatedNativeContextRebase.SeenAdmitted nextInputs secondAfter.native ∧
              ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output secondValue term ↔
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨firstAvailable, firstClosed, firstFuel, firstValue, firstAfter, first⟩ := generated_complete
    source facts formulas solver roots originals available closed state good contextual covered scopedCache
    semantic idle growth history left right leftAvailable rightAvailable leftClosed rightClosed ranges
  refine ⟨firstAvailable, firstClosed, firstFuel, firstValue, firstAfter, first.good, first, ?_⟩
  intro nextRanges
  obtain ⟨secondAvailable, secondClosed, secondFuel, secondValue, secondAfter, second⟩ := generated_complete
    state.native.machine.heap good.native.machine.1 formulas solver (roots ++ [left, right])
    (SourceCurrentAllocatedNativeGrownInventory.closed_originals state.native.machine.heap good.native.machine.1 (roots ++ [left, right]) firstAvailable firstClosed)
    firstAvailable firstClosed firstAfter first.good first.contextual first.covered first.scopedCache
    first.semantic first.idle first.extension.heap first.extension.history firstValue right
    first.result (first.keeps.available right rightAvailable) first.closed rightClosed nextRanges
  refine ⟨secondAvailable, secondClosed, secondFuel, secondValue, secondAfter, second.toWarmReceipt.done,
    second.closed, second.result, second.covered, second.covered.admitted, second.covered.seen_admitted, ?_⟩
  intro output term
  rw [second.meaning, first.meaning]
  exact ⟨fun proof => proof.1, fun proof => ⟨proof, proof.2⟩⟩
end Generated
end MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes

#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.execution_all_outcomes
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.execution_done_full_state
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.node_admission_before_publication
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.ordered_node_requests
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.concrete_trace_admission
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.fixed_query_exact_and_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.generated_inventory_retained
#print axioms MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.two_generated_queries

-- Complete integration signatures expose the initial and reached-range assumptions.
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.execution_all_outcomes
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.execution_done_full_state
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.node_admission_before_publication
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.ordered_node_requests
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.concrete_trace_admission
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.fixed_query_exact_and_covered
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.generated_inventory_retained
#check @MicroCFTA.SourceCurrentAllocatedNativeCoveredQueryIndependentProbes.two_generated_queries
