import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Fixed-input source scope of actual recursive requests

Initial closed operands supply the source certificate. Actual raw node
prefixes derive the reached request's operand scope and exact binding
membership in that fixed input heap. This result does not identify an
original source-program path.
-/
namespace MicroCFTA.SourceCurrentNativeRequestSourceScope
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial closed inputs derive the fixed-source scope of each actual reached node request. -/
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
    {count : Nat} (queried : NodeRequest Symbol Guard) (next : Node → Code Symbol Guard Node)
    {after : Checked (bits + 2)}
    (actual : Steps count (.code (requestNode emptyDomain left right)) before
      (.code (.node queried next)) after) :
    SourceRecursiveIntersectionInputView.NodeScope before.native.machine.heap queried ∧
      queried.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap := by
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
  exact SourceCurrentAllocatedRecursivePrefixScope.node_scope resources count
    (.code (requestNode request.domain request.left request.right)) before after _ current certificate
    (fun _ => trivial) queried next actual

end MicroCFTA.SourceCurrentNativeRequestSourceScope
