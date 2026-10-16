import MicroCFTA.SourceCurrentAllocatedNativeAdmissionNodeCertificates
open MicroCFTA MicroCFTA.Cache MicroCFTA.Language MicroCFTA.IntersectSchedule
open MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedProbeProvenance
open MicroCFTA.SourceRecursiveIntersectionKernel MicroCFTA.SourceRecursiveIntersectionThunks
open MicroCFTA.SourceRecursiveIntersectionCode MicroCFTA.SourceRecursiveIntersectionInputView
open MicroCFTA.SourceCurrentAllocatedNativeContextCache MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
open MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
open MicroCFTA.SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

-- Compilation retains admission through the actual protected finish continuation.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) (known : NodeCovered inputs request)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (semantic : SemanticReady machine.heap) (ready : NodeReady machine request)
    (growth : Grows source machine.heap) (history : Extends source.nodes.issued machine.heap.nodes.issued)
    (handle : Nat) :
    Certified source holds inputs ((compileNode request).bind (fun value => .finishNode handle value (.pure value)))
      machine (fun after value => Available after.heap value) := by
  apply certified_bind source holds inputs _ _ machine valid semantic _ _
    (SourceCurrentAllocatedNativeAdmissionNodeCertificates.node_certified source facts holds inputs request scope known
      machine valid semantic ready growth history)
  intro value after _ _ _ available
  exact available

-- A completed physical first body may precede another original request in the grown cache.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) (known : NodeCovered inputs request)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (semantic : SemanticReady machine.heap) (ready : NodeReady machine request)
    (growth : Grows source machine.heap) (history : Extends source.nodes.issued machine.heap.nodes.issued) :
    Certified source holds inputs ((compileNode request).bind (fun _ =>
      requestNode request.domain request.right request.left)) machine (fun after value => Available after.heap value) := by
  apply certified_bind source holds inputs _ _ machine valid semantic _ _
    (SourceCurrentAllocatedNativeAdmissionNodeCertificates.node_certified source facts holds inputs request scope known
      machine valid semantic ready growth history)
  intro _ after _ _ _ _
  exact requestNode_certified source holds inputs _ after
    (scope.swap source request.domain request.left request.right)
    ⟨SourceCurrentAllocatedNativeRequestAdmission.node_swap _ _ request known.1, known.2⟩

-- A source binder read admits a child before any of its node result laws are known.
example [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .reference (.interned name), other⟩)
    (known : NodeCovered inputs ⟨domain, .reference (.interned name), other⟩)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (semantic : SemanticReady machine.heap) (growth : Grows source machine.heap)
    (history : Extends source.nodes.issued machine.heap.nodes.issued) :
    Certified source holds inputs ((compileReference domain name other true).bind
      (fun value => .finishNode 0 value (.pure value))) machine (fun after value => Available after.heap value) := by
  apply certified_bind source holds inputs _ _ machine valid semantic _ _
    (SourceCurrentAllocatedNativeAdmissionNodeCertificates.left_reference_certified source holds inputs
      domain name other scope known machine valid growth history)
  intro value after _ _ _ available
  exact available
