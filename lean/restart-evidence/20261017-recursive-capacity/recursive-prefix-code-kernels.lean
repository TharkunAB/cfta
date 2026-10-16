import MicroCFTA.SourceCurrentAllocatedRecursiveDomainCode
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RecursivePrefixCodeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityRequiredSemanticCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual Mu entry preserves source bodies and records its literal seen pair. -/
theorem actual_mu_entry
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (member : request.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains source)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : NodeReady state request) (first second : Nat)
    (leftId : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightId : SourceRecursiveIntersectionControl.identity request.right = some second) :
    let entered := SourceRecursiveIntersectionEnvironment.enter state.domains request.domain.key
      request.left request.right first second
    let current : Machine Symbol Guard := {state with domains := entered.2}
    entered.1.key ∈ SourceRecursiveIntersectionSourceInventory.domains source ∧
    SourceRecursiveIntersectionControl.pair first second ∈ entered.1.key.seen ∧
    NodeScope source ⟨entered.1, body request.left, body request.right⟩ ∧
    SourceCurrentAllocatedRecursiveDomainCode.Certified source (SourceRecursiveIntersectionSourceInventory.domains source)
      (.node ⟨entered.1, body request.left, body request.right⟩
        (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))
      current (fun after value => Available after.heap value) := by
  have cert := SourceCurrentAllocatedRecursiveDomainCode.mu_certified source (SourceRecursiveIntersectionSourceInventory.domains source)
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts) request scope member state valid ready
  simp only [compileMu, leftId, rightId, SourceCurrentAllocatedRecursiveDomainCode.Certified] at cert
  have key := SourceRecursiveIntersectionSchedule.entered_key state.domains valid.2 request.domain.key
    request.left request.right first second
  refine ⟨?_, ?_, cert.2.2.2.1, cert.2.2.2⟩
  · rw [key]
    exact cert.1
  · rw [key]
    exact SourceRecursiveIntersectionEnvironment.enter_seen _ _ _ _ _

/-- A grown-heap read recovers the original Mu before the literal request. -/
theorem actual_read
    (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List IntersectionFlatMemoKeyDomain.DomainKey)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (present : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (other : Value Symbol Guard) (original : Original other) (available : Available source other)
    (member : domain.key ∈ inventory) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    ∃ bound, SourcePreparedSharedRows.read state.heap name = some bound ∧
      Original bound ∧ Available source bound ∧
      SourceCurrentAllocatedRecursiveDomainCode.Certified source inventory (requestNode domain bound other) state (fun after value => Available after.heap value) ∧
      SourceCurrentAllocatedRecursiveDomainCode.Certified source inventory (compileReference domain name other true) state (fun after value => Available after.heap value) := by
  obtain ⟨bound, found, boundOriginal, boundAvailable, _⟩ :=
    bindings.read source state.heap valid.1 growth history domain.key name present
  refine ⟨bound, found, boundOriginal, boundAvailable, ?_, ?_⟩
  · exact SourceCurrentAllocatedRecursiveDomainCode.requestNode_certified source inventory ⟨domain, bound, other⟩ state
      ⟨boundOriginal, original, boundAvailable, available, bindings⟩ member
  · exact SourceCurrentAllocatedRecursiveDomainCode.reference_certified source inventory domain name other true bindings original available member state valid growth history

/-- An actual checked prefix certifies its emitted code in the same returned machine. -/
theorem actual_checked_body {width : Nat}
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (member : request.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains source)
    (before after : SourceEqualityNativeDemand.State width) (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧
      SourceCurrentAllocatedRecursiveDomainCode.Certified source (SourceRecursiveIntersectionSourceInventory.domains source)
        (code.bind (fun value => .finishEdge 37 value (.pure value))) after.native.machine
        (fun final value => EdgeResident final.heap value) := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  refine ⟨same, ?_⟩
  apply SourceCurrentAllocatedRecursiveDomainCode.certified_bind source _ code _ after.native.machine
    (by simpa only [same] using valid) (by simpa only [same] using semantic)
    (fun final value => EdgeResident final.heap value) _
    (SourceCurrentAllocatedRecursiveDomainCode.body_certified source _ facts request scope member before after code valid semantic ready yielded)
  intro value final _ _ _ resident
  exact resident

#print axioms actual_mu_entry
#check @actual_mu_entry
#print axioms actual_read
#check @actual_read
#print axioms actual_checked_body
#check @actual_checked_body
end MicroCFTA.RecursivePrefixCodeKernels
