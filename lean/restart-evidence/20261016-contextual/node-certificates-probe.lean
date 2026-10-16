import MicroCFTA.SourceCurrentAllocatedNativeContextualNodeCertificates
open MicroCFTA
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionCode SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativeContextualCode
open SourceCurrentAllocatedNativeContextualNodeCertificates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

#print axioms empty_literal
#print axioms node_certified
#check @empty_literal
#check @node_certified

example (right : Value Symbol Guard) : (.empty : Value Symbol Guard) = .empty ∨ right = .empty :=
  empty_literal .empty right rfl

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified (view source holds) model ranked holds (compileNode request) state
      (fun _ value => NodeLaw (view source holds) model ranked holds request value) :=
  node_certified source facts holds model ranked request scope state valid semantic ready growth history
