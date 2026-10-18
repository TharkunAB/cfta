import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Checked native traces from initial closed operand admission

Initial available closed operands derive complete source syntax. Initial
source counters and domain headroom then admit every actual raw prefix.
The existing admission induction produces the physical trace checks.
Numeric width and store bounds follow that produced trace.

The initial native memo invariant retains exact keys and key safety.
Weak physical cell residency alone does not supply this invariant.
No future word range, input plan, checked trace, or result law is an input.
The theorem verifies actual prefixes and successful calls. It does not
prove that an arbitrary supplied fuel completes the call.
-/
namespace MicroCFTA.SourceCurrentNativeKeyAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "Stored" => InternedValueMassHeap.Stored
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial source admission turns a literal closed-request prefix into its checked trace and numeric bounds. -/
theorem node_prefix (bits : Nat) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    {count : Nat} {next : Control Node} {after : Checked (bits + 2)}
    (actual : Steps count (.code (requestNode emptyDomain left right)) before next after) :
    Trace count (.code (requestNode emptyDomain left right)) before next after ∧
    Good after ∧ SourceCurrentAllocatedNativeFieldClosure.Fields next after ∧
    Stored (massAfter count (initialBound before.native.machine.heap)) after.native.machine.heap ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit count (initialBound before.native.machine.heap) ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit count (initialBound before.native.machine.heap) ∧
    after.native.machine.domains.next ≤ before.native.machine.domains.next + count := by
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨emptyDomain,left,right⟩
  have facts := good.native.machine.1
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory before.native.machine.domains :=
    ⟨facts,SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts,good.native.machine.2,nodes,edges,by
      simpa only [inventory,source,SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified source inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
        (fun final value => Available final.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
      ⟨empty_domain _,leftAvailable,rightAvailable⟩ scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have admitted := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources count _ before next after _
    current certificate (fun _ => trivial) actual
  obtain ⟨_,_,final,fields,stored,nodeBound,edgeBound,domainBound⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.node_prefix request admitted.trace good ⟨empty_domain _,leftAvailable,rightAvailable⟩
  exact ⟨admitted.trace,final,fields,stored,nodeBound,edgeBound,domainBound⟩

/-- A literal successful closed request extracts its own checked trace from initial admission, without reached ranges. -/
theorem node_done (bits fuel : Nat) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    {result : Node} {after : Checked (bits + 2)}
    (actual : execute fuel (.code (requestNode emptyDomain left right)) before = .done result after) :
    ∃ count, count < fuel ∧ Trace count (.code (requestNode emptyDomain left right)) before (.code (.pure result)) after ∧
      Good after ∧ Available after.native.machine.heap result ∧
      Stored (massAfter count (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      InternedValueMass.value result ≤ massAfter count (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit count (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit count (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + count := by
  obtain ⟨count,below,raw⟩ := done_trace fuel _ before after result actual
  obtain ⟨checked,final,_,stored,nodeBound,edgeBound,domainBound⟩ :=
    node_prefix bits before good semantic left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room raw
  obtain ⟨_,available,_,_,_,_,_,_⟩ := SourceCurrentAllocatedNativeWidthTrace.node_prefix
    ⟨emptyDomain,left,right⟩ checked good ⟨empty_domain _,leftAvailable,rightAvailable⟩
  exact ⟨count,below,checked,final,available,stored,
    InternedValueMassHeap.available _ stored _ available,nodeBound,edgeBound,domainBound⟩

end MicroCFTA.SourceCurrentNativeKeyAdmission
