import MicroCFTA.SourceCurrentHereditaryNativeCompile

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryNativeCompileReviewKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
variable {Symbol Guard : Type}

/-- Two stored Mu operands derive actual entered bindings and the local optional-binder law. -/
theorem two_mu_compiler [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey)
    (leftBody leftDepth leftOrdinary rightBody rightDepth rightOrdinary : Value Symbol Guard)
    (leftAvailable : Available source (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightAvailable : Available source (.mu rightEntry rightBody rightDepth rightOrdinary))
    (leftAnnotated : Annotated annotation leftBody) (rightAnnotated : Annotated annotation rightBody)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : NodeReady state ⟨IntersectionEmptyDomain.emptyDomain,
      .mu leftEntry leftBody leftDepth leftOrdinary, .mu rightEntry rightBody rightDepth rightOrdinary⟩) :
    SourceCurrentHereditaryNativeScope.Bindings annotation source
      (SourceRecursiveIntersectionEnvironment.enter state.domains IntersectionEmptyDomain.emptyDomain.key
        (.mu leftEntry leftBody leftDepth leftOrdinary) (.mu rightEntry rightBody rightDepth rightOrdinary)
        leftEntry.identity rightEntry.identity).1.key ∧
    SourceCurrentHereditaryNativeCode.Certified annotation source (SourceCurrentHereditaryConstruction.MuStored annotation)
      (compileMu IntersectionEmptyDomain.emptyDomain (.mu leftEntry leftBody leftDepth leftOrdinary)
        (.mu rightEntry rightBody rightDepth rightOrdinary)) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  have left : Annotated annotation (.mu leftEntry leftBody leftDepth leftOrdinary) := .mu _ _ _ _ leftAnnotated
  have right : Annotated annotation (.mu rightEntry rightBody rightDepth rightOrdinary) := .mu _ _ _ _ rightAnnotated
  have bindings := SourceCurrentHereditaryNativeScope.empty annotation source
  constructor
  · exact bindings.enter annotation source _ _ _ leftAvailable rightAvailable left right state.domains valid.2 _ _
  · exact SourceCurrentHereditaryNativeCompile.mu_certified annotation source _
      (SourceCurrentHereditaryNativeCompile.causal_binders annotation)
      ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ bindings leftAvailable rightAvailable left right state valid ready

end MicroCFTA.HereditaryNativeCompileReviewKernels

#print axioms MicroCFTA.HereditaryNativeCompileReviewKernels.two_mu_compiler
#check @MicroCFTA.HereditaryNativeCompileReviewKernels.two_mu_compiler
