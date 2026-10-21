import MicroCFTA.SourceCurrentNativeRequestPositivePositions
import MicroCFTA.SourceCurrentNativePositiveSupportRebase
import MicroCFTA.SourceCurrentConstrainedCapCurrentNative

/-!
# Conditional native stores at an actual query return

The same completed trace supplies conditional cell laws and causal history.
Captured request origins rebase those laws to the actual returned heap.
The current operands need no root cap for this store-only conclusion.
-/
namespace MicroCFTA.SourceCurrentNativeCurrentStores
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentNativeRequestPositivePositions (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable {width : Nat}

/-- The same completed query returns current conditional stores and actual causal history without root caps. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {left right result : Node} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain before)
    (supported : Support before.native.machine.heap before.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    SourceCurrentConstrainedCapCurrentNative.At Plain after ∧
      Support after.native.machine.heap after.native ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) := by
  cases actual with
  | run trace =>
    let source := before.native.machine.heap
    let holds : Guard → Term Symbol → Bool := fun _ _ => true
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
    have facts := good.native.machine.1
    have known := SourceCurrentAllocatedRecursivePrefixState.initial source
      (SourceRecursiveIntersectionSourceInventory.domains source) before good semantic rfl
    have query := SourceCurrentNativeRequestPositivePositions.call_stores source facts before after left right result _
      known current.1 causal current.2.1 supported leftAvailable rightAvailable leftClosed rightClosed trace
    have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
    have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
    let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory source facts left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
    let inputs := inventory.inputs holds
    have originalInputs : ∀ input, inputs.valid input → SourceRecursiveIntersectionInputView.OriginalInput source input :=
      SourceCurrentAllocatedNativeInputInventoryModels.reachable_original source facts holds inventory.roots
        inventory.originals inventory.available inventory.closed
    have leftValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid source facts holds inventory.roots
      inventory.originals inventory.available inventory.closed left
      (by simp [inventory,SourceCurrentAllocatedNativeInventoryCold.pairInventory])
    have rightValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid source facts holds inventory.roots
      inventory.originals inventory.available inventory.closed right
      (by simp [inventory,SourceCurrentAllocatedNativeInventoryCold.pairInventory])
    have covered : SourceCurrentAllocatedNativeAdmissionCache.NodeCovered inputs request :=
      ⟨⟨leftOriginal,rightOriginal,leftValid,rightValid⟩,SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
    have scope := SourceRecursiveIntersectionCode.initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
    have certificate := SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs request
      before.native.machine scope covered
    have captured := SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins source holds inputs facts
      originalInputs trace (fun final value => Available final.heap value) good semantic
      (grows_refl _) (extends_refl _) (fun _ => trivial) current.2.2 certificate
    have next := SourceCurrentConstrainedCapCurrentNative.rebase Plain source after facts
      query.2.1.current.good query.2.1.context query.2.1.stored captured.1
    have rebased := SourceCurrentNativePositiveSupportRebase.rebase source after.native.machine.heap after.native
      facts query.2.1.context.valid.1 query.2.1.context.growth query.2.1.context.history captured.1 query.1
    exact ⟨next,rebased,query.2.2⟩

end MicroCFTA.SourceCurrentNativeCurrentStores

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentNativeCurrentStores.step
#print MicroCFTA.SourceCurrentNativeCurrentStores.step
#print axioms MicroCFTA.SourceCurrentNativeCurrentStores.step
