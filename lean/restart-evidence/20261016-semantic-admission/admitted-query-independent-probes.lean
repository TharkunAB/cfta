import MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery

#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery.query_complete
#check MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement
#check MicroCFTA.SourceCurrentAllocatedNativeAdmittedQuery.query_complete

namespace MicroCFTA.SourceCurrentAllocatedNativeAdmittedQueryProbes
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeContextRebase
open SourceCurrentAllocatedNativeAdmittedQuery
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

section Query
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  (source : State Symbol Guard) (sourceFacts : InternedNestedFacts.Facts source)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (roots : List (Value Symbol Guard)) (originals : ∀ root ∈ roots, Original root)
  (available : Values source roots) (closed : ∀ root ∈ roots, root.free = [])
local notation "holds" => SourceEqualityPCSGuard.holds formulas solver
local notation "oldView" => view source holds
local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed
variable (state : Checked width) (good : SourceCurrentAllocatedNativePhysicalCompletion.Good state)
  (contextual : SourceCurrentAllocatedNativeContextCache.Contextual oldView
    (finiteInputMeaning oldView oldInputs) (finiteRankedInput oldView oldInputs) holds state.native)
  (admitted : SourceCurrentAllocatedNativeInputModelTransport.Admitted oldView
    (finiteInputMeaning oldView oldInputs) state.native)
  (seen : SeenAdmitted oldInputs state.native)
  (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
  (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.native.machine.heap)
  (idle : SourceRecursiveIntersectionNative.Idle state.native)
  (growth : Grows source state.native.machine.heap)
  (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
  (left right : Value Symbol Guard)
  (leftAvailable : Available state.native.machine.heap left)
  (rightAvailable : Available state.native.machine.heap right)
  (leftClosed : left.free = []) (rightClosed : right.free = [])
  (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state)
include source sourceFacts formulas solver roots originals available closed state good contextual admitted seen
  scopedCache semantic idle growth history left right leftAvailable rightAvailable leftClosed rightClosed ranges

-- Kernel integration 1: derive actual done, closedness, and exact physical language.
-- No law or validity premise for the new target model is supplied.
example : ∃ fuel value after,
    SourceEqualityNativeDemand.execute (fuel + 1)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
    value.free = [] ∧
    ∀ output term, InternedGuardedLanguage.meaning holds output value term ↔
      InternedGuardedLanguage.meaning holds output left term ∧
      InternedGuardedLanguage.meaning holds output right term := by
  obtain ⟨inputs, fuel, value, after, receipt⟩ := query_complete source sourceFacts formulas solver roots
    originals available closed state good contextual admitted seen scopedCache semantic idle growth history
    left right leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel, value, after, receipt.done, receipt.closed, receipt.meaning⟩

-- Kernel integration 2: the same actual return derives result syntax and final physical fields.
example : ∃ fuel value after,
    SourceEqualityNativeDemand.execute (fuel + 1)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
    Available after.native.machine.heap value ∧ Original value ∧
    SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap ∧
    SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧ SourceRecursiveIntersectionNative.Idle after.native := by
  obtain ⟨inputs, fuel, value, after, receipt⟩ := query_complete source sourceFacts formulas solver roots
    originals available closed state good contextual admitted seen scopedCache semantic idle growth history
    left right leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel, value, after, receipt.done, receipt.result,
    SourceRecursiveIntersectionOriginalOutput.closed_original value after.native.machine.heap
      receipt.good.native.machine.1.coherent receipt.result receipt.closed,
    receipt.good.fields, receipt.scopedCache, receipt.idle⟩
end Query

-- Kernel integration 3: actual grown inventories derive admission and exact old-input ranks.
example {S G : Type} (source target : State S G)
    (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
    (growth : Grows source target) (history : Extends source.nodes.issued target.nodes.issued)
    (holds : G → Term S → Bool) (roots : List (Value S G))
    (originals : ∀ root ∈ roots, Original root) (available : Values source roots)
    (closed : ∀ root ∈ roots, root.free = []) (targetRoots : List (Value S G))
    (targetAvailable : Values target targetRoots) (targetClosed : ∀ root ∈ targetRoots, root.free = [])
    (included : ∀ root ∈ roots, root ∈ targetRoots) (input : Input)
    (known : (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots
      originals available closed).valid input) (rank : Nat) (term : Term S) :
    let newInputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput target targetFacts holds targetRoots
      (SourceCurrentAllocatedNativeGrownInventory.closed_originals target targetFacts targetRoots targetAvailable targetClosed)
      targetAvailable targetClosed
    newInputs.valid input ∧
      (inputAt (finiteRanks (view target holds) newInputs) input rank term ↔
        inputAt (finiteRanks (view source holds) (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
          source sourceFacts holds roots originals available closed)) input rank term) := by
  have agreement := inventory_agreement source target sourceFacts targetFacts growth history holds roots
    originals available closed targetRoots targetAvailable targetClosed included
  exact ⟨agreement.valid input known, agreement.rank input known rank term⟩
end MicroCFTA.SourceCurrentAllocatedNativeAdmittedQueryProbes
