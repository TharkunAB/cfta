import MicroCFTA.SourceRecursiveIntersectionCodeBounds
import MicroCFTA.IntersectMuCalls

/-!
# Strict limits of actual compiled Mu requests

Original body readback, physical branch selection, and canonical domain
allocation derive the smaller child bound for all three Mu branches.
The optional-binder continuation retains the limit at its actual machine.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule SourceRecursiveIntersectionRequestProgress

/-- Original actual source bodies have the exact semantic body-input codec. -/
theorem body_encoded (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value) (available : Available source value) :
    inputOf (SourceRecursiveIntersectionKernel.body value) = bodyInput (view source holds) (inputOf value) := by
  cases original <;> try rfl
  case mu entry body depth ordinary original =>
    exact (body_readback source facts holds entry body depth ordinary available).symm

/-- Original physical branch selection has the exact complete semantic decision. -/
theorem decision_source [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request) :
    SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right =
      inputDecision (SourceRecursiveIntersectionSchedule.domain request.domain.key)
        (closed (view source holds) (inputOf request.left)) (closed (view source holds) (inputOf request.right))
        (inputOf request.left) (inputOf request.right) := by
  rw [decision_encoded request.domain.key request.left request.right (inputOf request.left) (inputOf request.right)
    (scope.left.codec request.left) (scope.right.codec request.right),
    ← closed_readback source facts holds request.left scope.left scope.leftAvailable,
    ← closed_readback source facts holds request.right scope.right scope.rightAvailable]

/-- Actual canonical Mu entry derives an original child strictly below the parent request bound. -/
theorem mu_request_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (recursive : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second) :
    NodeBelow source holds (requiredFuel (view source holds) (nodeSemantic request) complete)
      ⟨(SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ := by
  have selected := decision_source source facts holds request scope
  have member := mu_child_member (view source holds) (SourceRecursiveIntersectionSchedule.domain request.domain.key)
    (inputOf request.left) (inputOf request.right) _ selected.symm recursive
  obtain ⟨semantic, smaller⟩ := physical_child_requiredFuel source facts holds request.domain.key request.left request.right
    scope.left scope.right scope.leftAvailable scope.rightAvailable complete _ member
  simp only [muChild, ← body_encoded source facts holds request.left scope.left scope.leftAvailable,
    ← body_encoded source facts holds request.right scope.right scope.rightAvailable] at semantic smaller
  obtain ⟨physical, equal⟩ := entered_requiredFuel (view source holds) cache valid request.domain.key request.left request.right
    (inputOf request.left) (inputOf request.right) (scope.left.codec request.left) (scope.right.codec request.right)
    first second leftIdentity rightIdentity _ _ semantic
  refine ⟨scope.mu source request.domain _ request.left request.right first second (entered_key cache valid _ _ _ first second), physical, ?_⟩
  rw [← equal] at smaller
  exact smaller

/-- Every selected compiled Mu body retains its strict request limit through actual canonical allocation. -/
theorem compileMu_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (recursive : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Below source holds (requiredFuel (view source holds) (nodeSemantic request) complete)
      (compileMu request.domain request.left request.right) state := by
  cases first : SourceRecursiveIntersectionControl.identity request.left <;>
    cases second : SourceRecursiveIntersectionControl.identity request.right <;>
    simp only [compileMu, first, second, unsupported, Below] <;> try trivial
  refine ⟨mu_request_below source facts holds request scope complete recursive state.domains valid.2 _ _ first second, ?_⟩
  intro value after _ _ _ result final done
  trivial

end MicroCFTA.SourceRecursiveIntersectionCode
