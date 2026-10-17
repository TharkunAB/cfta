import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 1000000

namespace MicroCFTA.WarmInitialRangesKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeRequestBounds (Words WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial counters admit an arbitrary warm prefix and bound its actual allocated domains. -/
theorem reached_words_and_domain_supply (bits : Nat) (before : Checked (bits + 2))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (fuel : Nat) (next : Control (Value Symbol Guard)) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before next after) :
    Words (bits + 2) next ∧ WordRanges next after ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
        before.native.machine.domains after.native.machine.domains ∧
      after.native.machine.domains.next < 2 ^ (bits + 1) := by
  have initial := SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before good semantic
    left right leftOriginal rightOriginal leftAvailable rightAvailable nodes edges room
  have allocation := SourceCurrentAllocatedNativeDomainTrace.trace
    (SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
    fuel _ next before after actual initial.2
  have bound := allocation.next_le
  rw [SourceRecursiveIntersectionSourceInventory.domains_length] at bound
  exact ⟨initial.1 fuel next after actual,
    WordRanges.after_trace _ next before after initial.1 fuel actual, allocation, Nat.lt_of_le_of_lt bound room⟩

#print axioms reached_words_and_domain_supply
#check @reached_words_and_domain_supply
end MicroCFTA.WarmInitialRangesKernels
