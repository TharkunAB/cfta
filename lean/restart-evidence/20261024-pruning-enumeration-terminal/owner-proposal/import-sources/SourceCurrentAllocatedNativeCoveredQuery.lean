import MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace
import MicroCFTA.SourceCurrentAllocatedNativeAdmissionNodeCertificates
import MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
import MicroCFTA.SourceCurrentAllocatedNativeWarmQuery
import MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery

/-!
# Exact native queries that retain causal memo admission

Actual source certificates derive admission through the returned physical trace.
Every final suspended, evaluating, or returned cell retains its original
request admission and captured pair coverage. A later inventory expansion
can therefore retain the same warm tables without a new coverage premise.
Initial all-cell coverage and reached machine ranges remain explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
open SourceCurrentAllocatedNativeAdmissionCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Actual source node and checked edge branches derive both static certificate families. -/
theorem branches [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds)) :
    SourceCurrentAllocatedNativeAdmissionTrace.Branches (width := width) source holds inputs :=
  ⟨SourceCurrentAllocatedNativeAdmissionNodeCertificates.node_certified source facts holds inputs,
    SourceCurrentAllocatedNativeAdmissionEdgeCertificates.body_certified source facts holds inputs⟩

/-- An exact closed return retains causal admission for all actual final native cells. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) : Prop
    extends toWarmReceipt : SourceCurrentAllocatedNativeWarmQuery.Receipt
      source formulas solver inputs fuel left right before value after where
  covered : Covered inputs after.native

/-- Fixed-model query execution derives admission of each newly published internal request. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (state : Checked width) (good : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (covered : Covered inputs state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap)
    (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right))
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after, Receipt source formulas solver inputs fuel left right state value after := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have known : NodeCovered inputs request :=
    ⟨⟨leftOriginal, rightOriginal, leftValid, rightValid⟩,
      SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
  have certificate := SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified
    source holds inputs request state.native.machine scope known
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeWarmQuery.query_complete
    source facts formulas solver inputs state good contextual scopedCache semantic idle growth history
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges
  have retained := SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered source holds inputs
    (branches source facts holds inputs) receipt.trace (fun final value => Available final.heap value)
    good semantic growth history (fun _ => trivial) covered certificate
  exact ⟨fuel, value, after, receipt, retained.1⟩

section Generated
variable (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
  (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
local notation "holds" => SourceEqualityPCSGuard.holds formulas solver
local notation "oldView" => view source holds
local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source facts holds roots originals available closed

/-- Actual model growth admits generated operands and derives coverage for every next final cell. -/
theorem generated_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (good : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual oldView
      (finiteInputMeaning oldView oldInputs) (finiteRankedInput oldView oldInputs) holds state.native)
    (covered : Covered oldInputs state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap)
    (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    let target := state.native.machine.heap
    let targetRoots := roots ++ [left, right]
    ∃ targetAvailable : Values target targetRoots,
      ∃ targetClosed : ∀ root ∈ targetRoots, root.free = [],
        ∃ fuel value after, Receipt target formulas solver
          (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput target good.native.machine.1 holds targetRoots
            (SourceCurrentAllocatedNativeGrownInventory.closed_originals target good.native.machine.1
              targetRoots targetAvailable targetClosed) targetAvailable targetClosed)
          fuel left right state value after := by
  let target := state.native.machine.heap
  have targetFacts : InternedNestedFacts.Facts target := good.native.machine.1
  let targetRoots := roots ++ [left, right]
  have targetAvailable : Values target targetRoots := by
    intro root member
    change root ∈ roots ++ [left, right] at member
    rcases List.mem_append.mp member with old | next
    · exact (available root old).grows source target growth history
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftAvailable
      · exact rightAvailable
  have targetClosed : ∀ root ∈ targetRoots, root.free = [] := by
    intro root member
    change root ∈ roots ++ [left, right] at member
    rcases List.mem_append.mp member with old | next
    · exact closed root old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftClosed
      · exact rightClosed
  have included : ∀ root ∈ roots, root ∈ targetRoots := fun _ member => List.mem_append.mpr (Or.inl member)
  have targetOriginals := SourceCurrentAllocatedNativeGrownInventory.closed_originals
    target targetFacts targetRoots targetAvailable targetClosed
  let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
    target targetFacts holds targetRoots targetOriginals targetAvailable targetClosed
  have agreement : SourceCurrentAllocatedNativeContextRebase.Agreement oldInputs inputs :=
    SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement source target facts targetFacts growth history holds
      roots originals available closed targetRoots targetAvailable targetClosed included
  have targetContextual := SourceCurrentAllocatedNativeContextRebase.contextual agreement holds state.native
    covered.admitted covered.seen_admitted contextual
  have targetCovered := covered.rebase agreement
  have leftMember : left ∈ targetRoots := by simp [targetRoots]
  have rightMember : right ∈ targetRoots := by simp [targetRoots]
  obtain ⟨fuel, value, after, receipt⟩ := query_complete target targetFacts formulas solver inputs state good
    targetContextual targetCovered scopedCache semantic idle (grows_refl target) (extends_refl target.nodes.issued)
    left right (targetOriginals left leftMember) (targetOriginals right rightMember)
    leftAvailable rightAvailable leftClosed rightClosed
    (SourceCurrentAllocatedNativeGrownInventory.target_root_valid target targetFacts holds targetRoots
      targetAvailable targetClosed left leftMember)
    (SourceCurrentAllocatedNativeGrownInventory.target_root_valid target targetFacts holds targetRoots
      targetAvailable targetClosed right rightMember) ranges
  exact ⟨targetAvailable, targetClosed, fuel, value, after, receipt⟩
end Generated
end MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery
