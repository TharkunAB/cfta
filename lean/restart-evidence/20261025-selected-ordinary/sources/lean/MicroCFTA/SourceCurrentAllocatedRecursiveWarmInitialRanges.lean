import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges

/-!
# Initial numeric admission with actual warm checked tables

The query-entry heap fixes the original operand source. Initial counters and
finite domain-inventory headroom derive every reached word and enter check.
The supplied native tables and equality operations remain unchanged at entry.
No idle condition or completed execution is needed for these range predicates.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentAllocatedRecursivePrefixAdmission (Resources)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial query-entry counters admit every raw prefix with the same actual warm tables. -/
theorem warm_initial_ranges (bits : Nat) (before : Checked (bits + 2))
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
    WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before ∧
      SourceCurrentAllocatedNativeDomainTrace.Prefixes
        (SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have resources : Resources bits source inventory before.native.machine.domains :=
    ⟨good.native.machine.1, SourceCurrentAllocatedRecursiveDomainCode.source_closed source good.native.machine.1,
      good.native.machine.2, nodes, edges, by
        simpa only [inventory, source, SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current : Current source inventory before.native.machine.domains before :=
    SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have certificate : Certified source inventory (.code (requestNode request.domain request.left request.right))
      before.native.machine (fun after value => Available after.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
      ⟨empty_domain _, leftAvailable, rightAvailable⟩ scope
      (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  exact ⟨SourceCurrentAllocatedRecursiveInitialRanges.word_ranges resources _ before _ current certificate (fun _ => trivial),
    SourceCurrentAllocatedRecursiveInitialRanges.domain_prefixes resources _ before _ current certificate (fun _ => trivial)⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
