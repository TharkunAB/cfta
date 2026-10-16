import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.NodeInputs
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.NodeInputs
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.EdgeInputs
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.EdgeInputs
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.Certified
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.Certified
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.certified_bind
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.certified_bind
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.request_node
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.request_node
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.request_edge
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.request_edge
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.certified_walk
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode.certified_walk

namespace MicroCFTA.FiniteOrdinaryCodeProbes
open InternedConstructorTemplates SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryCode SourceCurrentAllocatedFiniteOrdinaryStored
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Repeated ordered occurrences retain their own node request certificates. -/
theorem repeated_empty [DecidableEq (EdgeKey Symbol Guard)]
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap) :
    Certified (walk (fun _ : Unit => requestNode IntersectionEmptyDomain.emptyDomain .empty .empty) [(), ()]) state
      (fun _ values => Language.All₂ (fun (_ : Unit) value =>
        NodeCertificate ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩ value) [(), ()] values) := by
  apply certified_walk _ _ state valid semantic
  intro _input _member after _afterValid _growth _afterSemantic
  exact request_node ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩ after ⟨rfl, .empty, .empty⟩

/-- Explicit finish instructions require a separate controlled native frame proof. -/
theorem finish_needs_frame [DecidableEq (EdgeKey Symbol Guard)]
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → Unit → Prop) :
    ¬ Certified (.finishNode 0 .empty (.pure ())) state post := by
  intro impossible
  exact impossible

#print axioms repeated_empty
#check @repeated_empty
#print axioms finish_needs_frame
#check @finish_needs_frame
end MicroCFTA.FiniteOrdinaryCodeProbes
