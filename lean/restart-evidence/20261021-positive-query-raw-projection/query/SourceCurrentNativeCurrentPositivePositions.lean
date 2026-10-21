import MicroCFTA.SourceCurrentNativeRequestPositivePositions
import MicroCFTA.SourceCurrentNativePositiveSupportRebase
import MicroCFTA.SourceCurrentConstrainedCapCurrentNative

/-!
# Same-query positional support at the returned current heap

The actual completed trace supplies both its result law and its new cells.
Captured origins at the entry source justify rebasing those same cells.
-/
namespace MicroCFTA.SourceCurrentNativeCurrentPositivePositions
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentNativeRequestPositivePositions (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable {width : Nat}

/-- The same actual query returns its cap, positive ancestry, and current positional cell laws. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {left right result : Node} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain before)
    (supported : Support before.native.machine.heap before.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right) :
    SourceCurrentConstrainedCapCurrentNative.At Plain after ∧
      Support after.native.machine.heap after.native ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      Cap Plain depth result ∧
      ∀ path, PositiveAt result path → PositiveAt left path ∨ PositiveAt right path := by
  cases actual with
  | run trace =>
    let source := before.native.machine.heap
    let holds := SourceEqualityPCSGuard.holds formulas solver
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
    have facts := good.native.machine.1
    have known := SourceCurrentAllocatedRecursivePrefixState.initial source
      (SourceRecursiveIntersectionSourceInventory.domains source) before good semantic rfl
    have query := SourceCurrentNativeRequestPositivePositions.call source facts depth before after left right result _
      known current.1 causal current.2.1 supported leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap trace
    have next := SourceCurrentConstrainedCapCurrentNative.step depth formulas solver (.run trace) good semantic current
      leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap
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
    have rebased := SourceCurrentNativePositiveSupportRebase.rebase source after.native.machine.heap after.native
      facts query.2.2.1.context.valid.1 query.2.2.1.context.growth query.2.2.1.context.history captured.1 query.1
    exact ⟨next.1,rebased,query.2.2.2,next.2.1,query.2.1⟩

end MicroCFTA.SourceCurrentNativeCurrentPositivePositions
