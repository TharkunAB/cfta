import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

namespace MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
/-- Source counters and current domain room bound every direct edge-body prefix. -/
theorem edge_body (bits : Nat)
    (source : InternedConstructorTemplates.State Symbol Guard) (state : Checked (bits + 2))
    (facts : Facts source)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good state)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.native.machine.heap)
    (growth : Grows source state.native.machine.heap)
    (history : Cache.Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : EdgeValue Symbol Guard)
    (scope : EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
    (ready : EdgeReady state.native.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next, state.native.machine.domains.next, 0⟩) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.edgeBody ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state := by
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory
      state.native.machine.domains :=
    ⟨facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts,
      good.native.machine.2, room.1, room.2.1, by
        simpa only [inventory, SourceRecursiveIntersectionSourceInventory.domains_length] using room.2.2⟩
  have current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory
      state.native.machine.domains state :=
    ⟨good, semantic, growth, history, .refl _⟩
  have member : request.domain.key ∈ inventory :=
    SourceRecursiveIntersectionSourceInventory.empty_mem source
  have certificate := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
    state.native.machine scope member ready
  exact SourceCurrentAllocatedRecursiveInitialRanges.word_ranges resources (.edgeBody request .pure)
    state (fun after value => InternedEdgeResidency.EdgeResident after.heap value) current certificate ⟨ready, fun _ => trivial⟩

end MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.edge_body
#print MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.edge_body
#print axioms MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.edge_body
