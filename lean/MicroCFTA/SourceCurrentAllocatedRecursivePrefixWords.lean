import MicroCFTA.SourceRecursiveIntersectionDomainAllocation
import MicroCFTA.SourceRecursiveIntersectionSourceInventory
import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution

/-!
# Current request words from initial source and domain supplies

Original operands retain their initial source identities. The actual domain
allocation history bounds the current shifted domain identity. These local
request checks require no completed or physically annotated prefix.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixWords
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open IntersectionFlatMemoKeyDomain
open SourceCurrentAllocatedNativeRequestBounds (Words)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocation" => SourceRecursiveIntersectionDomainAllocation.Trace
variable {A : Type}

/-- Actual sequential allocation and initial headroom bound the shifted current domain. -/
theorem domain_lt (bits : Nat) (inventory : List DomainKey) (initial current : Cache.State DomainKey)
    (domain : Interned DomainKey) (trace : Allocation inventory initial current) (valid : Cache.Valid initial)
    (represented : IntersectionEmptyDomain.Represents current domain.key domain)
    (room : initial.next + inventory.length < 2 ^ (bits + 1)) : domain.identity < 2 ^ (bits + 1) :=
  trace.identity_lt valid represented room

/-- A current node instruction uses original operand keys and its actual represented domain. -/
theorem node_words (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (state : Checked (bits + 2)) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (scope : NodeScope source request)
    (known : Domain state.native.machine request.domain)
    (trace : Allocation inventory initial state.native.machine.domains) (valid : Cache.Valid initial)
    (nodes : source.nodes.next < 2 ^ bits) (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    Words (bits + 2) (.code (.node request next)) :=
  fun key encoded => SourceRecursiveIntersectionSourceInventory.node_key_safe bits source facts nodes request scope
    (domain_lt bits inventory initial state.native.machine.domains request.domain trace valid known.represented room) key encoded

/-- A current edge instruction uses original resident rows and its actual represented domain. -/
theorem edge_words (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (state : Checked (bits + 2)) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (scope : EdgeScope source request)
    (known : Domain state.native.machine request.domain)
    (trace : Allocation inventory initial state.native.machine.domains) (valid : Cache.Valid initial)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    Words (bits + 2) (.code (.edge request next)) :=
  SourceRecursiveIntersectionSourceInventory.edge_key_safe bits source facts edges request scope
    (domain_lt bits inventory initial state.native.machine.domains request.domain trace valid known.represented room)

/-- Actual heap and issuance growth derive node residency before the physical demand check. -/
theorem node_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (state : Checked (bits + 2)) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (scope : NodeScope source request)
    (known : Domain state.native.machine request.domain)
    (trace : Allocation inventory initial state.native.machine.domains) (valid : Cache.Valid initial)
    (nodes : source.nodes.next < 2 ^ bits) (room : initial.next + inventory.length < 2 ^ (bits + 1))
    (growth : Grows source state.native.machine.heap)
    (history : Cache.Extends source.nodes.issued state.native.machine.heap.nodes.issued) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.node request next)) state :=
  ⟨⟨known, scope.leftAvailable.grows source state.native.machine.heap growth history,
    scope.rightAvailable.grows source state.native.machine.heap growth history⟩,
    node_words bits source facts inventory initial state request next scope known trace valid nodes room⟩

/-- Actual edge-record growth derives row residency before the physical demand check. -/
theorem edge_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (state : Checked (bits + 2)) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (scope : EdgeScope source request)
    (known : Domain state.native.machine request.domain)
    (trace : Allocation inventory initial state.native.machine.domains) (valid : Cache.Valid initial)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) (room : initial.next + inventory.length < 2 ^ (bits + 1))
    (growth : Grows source state.native.machine.heap) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.edge request next)) state :=
  ⟨⟨known, edge_grows source state.native.machine.heap growth request.left scope.leftResident,
    edge_grows source state.native.machine.heap growth request.right scope.rightResident⟩,
    edge_words bits source facts inventory initial state request next scope known trace valid edges room⟩

/-- The reserved empty domain needs no domain-cache capacity or allocation history. -/
theorem node_words_empty (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right : Value Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (scope : NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
    (nodes : source.nodes.next < 2 ^ bits) :
    Words (bits + 2) (.code (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ next)) :=
  fun key encoded => SourceRecursiveIntersectionSourceInventory.node_key_safe bits source facts nodes _ scope
    (Nat.two_pow_pos _) key encoded

/-- Empty-domain row requests likewise need only the initial raw edge supply. -/
theorem edge_words_empty (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right : EdgeValue Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (scope : EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) :
    Words (bits + 2) (.code (.edge ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ next)) :=
  SourceRecursiveIntersectionSourceInventory.edge_key_safe bits source facts edges _ scope (Nat.two_pow_pos _)

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixWords
