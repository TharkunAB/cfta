import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWords

/-!
# Finite ordinary native queries from initial key bounds

Initial operand keys derive every reached word check.
The finite endpoint constructs its own checked receipt and result bounds.
The supply adapter reads only the two initial constructor counters.
This result does not bound the counters after the query or a later query.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryBoundedFinite
open Cache InternedConstructorTemplates InternedProbeProvenance
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

/-- Initial recursive operand keys suffice for finite execution with both original height bounds. -/
theorem finite (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (state : Checked (bits + 2))
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftKeys : KNode bits left) (rightKeys : KNode bits right) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ DNode value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] := by
  exact SourceCurrentAllocatedFiniteOrdinaryFinite.finite holds state good semantic stored idle
    left right leftAvailable rightAvailable leftKeys.domain rightKeys.domain
    (SourceCurrentAllocatedFiniteOrdinaryWords.node bits state good left right
      leftAvailable rightAvailable leftKeys rightKeys)

/-- Initial supply bounds and resident domain operands construct the same complete finite receipt. -/
theorem of_domain (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (state : Checked (bits + 2))
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (nodes : state.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ DNode value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] := by
  exact SourceCurrentAllocatedFiniteOrdinaryFinite.finite holds state good semantic stored idle
    left right leftAvailable rightAvailable leftDomain rightDomain
    (SourceCurrentAllocatedFiniteOrdinaryWords.node_of_domain bits state good nodes edges
      left right leftAvailable rightAvailable leftDomain rightDomain)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryBoundedFinite
