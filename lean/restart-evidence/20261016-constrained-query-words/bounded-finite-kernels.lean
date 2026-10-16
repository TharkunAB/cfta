import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryBoundedFinite

namespace FiniteOrdinaryBoundedFiniteKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryStored
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "KNode" => SourceCurrentAllocatedFiniteOrdinaryKeys.Node
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Two constructed executions share their actual warm state and original bounded operands. -/
theorem warm_originals (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (state : Checked (bits + 2))
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right) :
    ∃ fuel value after second result final,
      SourceEqualityNativeDemand.execute (fuel + 1) (.code (requestNode emptyDomain left right)) state = .done value after ∧
      SourceEqualityNativeDemand.execute (second + 1) (.code (requestNode emptyDomain left right)) after = .done result final ∧
      Good final ∧ Stored final.native ∧ DNode result ∧
      height result ≤ height left ∧ height result ≤ height right := by
  obtain ⟨fuel, value, after, first, afterIdle, afterSemantic, afterStored, _⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryBoundedFinite.finite bits holds state good semantic stored idle
      left right leftAvailable rightAvailable leftKeys rightKeys
  obtain ⟨second, result, final, next, _finalIdle, _finalSemantic, finalStored, domain, leftHeight, rightHeight, _⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryBoundedFinite.finite bits holds after first.good afterSemantic afterStored afterIdle
      left right (first.extension.available left leftAvailable) (first.extension.available right rightAvailable) leftKeys rightKeys
  exact ⟨fuel, value, after, second, result, final, first.done, next.done, next.good,
    finalStored, domain, leftHeight, rightHeight⟩

/-- Initial counter bounds give actual interpreter success without a future word plan. -/
theorem constructed_execution (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (state : Checked (bits + 2))
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (nodes : state.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right) :
    ∃ fuel value after,
      SourceEqualityNativeDemand.execute (fuel + 1) (.code (requestNode emptyDomain left right)) state = .done value after ∧
      Good after ∧ Available after.native.machine.heap value ∧ DNode value ∧
      height value ≤ height left ∧ height value ≤ height right := by
  obtain ⟨fuel, value, after, receipt, _afterIdle, _afterSemantic, _afterStored, domain, leftHeight, rightHeight, _⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryBoundedFinite.of_domain bits holds state good semantic stored idle
      nodes edges left right leftAvailable rightAvailable leftDomain rightDomain
  exact ⟨fuel, value, after, receipt.done, receipt.good, receipt.result, domain, leftHeight, rightHeight⟩

end FiniteOrdinaryBoundedFiniteKernels
#print axioms FiniteOrdinaryBoundedFiniteKernels.warm_originals
#check @FiniteOrdinaryBoundedFiniteKernels.warm_originals
#print axioms FiniteOrdinaryBoundedFiniteKernels.constructed_execution
#check @FiniteOrdinaryBoundedFiniteKernels.constructed_execution
