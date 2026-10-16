import MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
import MicroCFTA.SourceCurrentAllocatedNativeContextualMuCertificates
import MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates

/-!
# Local contextual certificates for the complete source node dispatcher

The actual guard order selects a direct law or a certified source branch.
Recursive branch certificates use only exact child laws. No parent execution
or parent language law supplies this dispatch certificate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualNodeCertificates
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativeContextualCode
open SourceCurrentAllocatedNativeContextualCertificates
open SourceCurrentAllocatedNativeContextualMuCertificates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual empty rejection has a literal empty operand. -/
theorem empty_literal (left right : Value Symbol Guard) (selected : hasEmpty left right = true) :
    left = .empty ∨ right = .empty := by
  cases left <;> cases right <;> simp_all [hasEmpty, Value.referenceOf]

/-- Every actual original source node branch has its independently derived local certificate. -/
theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified (view source holds) model ranked holds (compileNode request) state
      (fun _ value => NodeLaw (view source holds) model ranked holds request value) := by
  cases request with
  | mk domain left right =>
      by_cases empty : hasEmpty left right = true
      · have selected := empty_first domain.key left right empty
        simpa only [compileNode, selected] using empty_certified (view source holds) model ranked holds
          ⟨domain, left, right⟩ (empty_literal left right empty) state
      by_cases restart : reset domain.key left right = true
      · have selected : decision domain.key left right = .reset := by simp [decision, empty, restart]
        simpa only [compileNode, selected] using reset_certified (view source holds) model ranked holds ⟨domain, left, right⟩ state
      by_cases self : closedSelf left right = true
      · have selected : decision domain.key left right = .self := by simp [decision, empty, restart, self]
        simpa only [compileNode, selected] using self_certified source facts holds model ranked ⟨domain, left, right⟩
          scope.leftAvailable scope.rightAvailable self state
      by_cases swap : greater left right = true
      · have selected : decision domain.key left right = .swap := by simp [decision, empty, restart, self, swap]
        simpa only [compileNode, selected] using swap_certified (view source holds) model ranked holds ⟨domain, left, right⟩ state
      cases first : identity left with
      | none => simp [compileNode, decision, empty, restart, self, swap, first, SourceRecursiveIntersectionCode.unsupported, Certified]
      | some firstName =>
          cases second : identity right with
          | none => simp [compileNode, decision, empty, restart, self, swap, first, second, SourceRecursiveIntersectionCode.unsupported, Certified]
          | some secondName =>
              by_cases seen : pair firstName secondName ∈ domain.key.seen
              · have selected : decision domain.key left right = .repeated (pair firstName secondName) := by
                  simp [decision, empty, restart, self, swap, first, second, seen]
                simpa only [compileNode, selected] using repeated_certified (view source holds) model ranked holds
                  ⟨domain, left, right⟩ firstName secondName first second
                  (identity_nonempty left scope.left firstName first) (identity_nonempty right scope.right secondName second) seen state
              have selected : decision domain.key left right = SourceRecursiveIntersectionControl.payload left right := by
                simp [decision, empty, restart, self, swap, first, second, seen]
              cases scope.left <;> cases scope.right
              all_goals simp only [SourceRecursiveIntersectionControl.payload] at selected
              all_goals rw [compileNode, selected]
              all_goals first
                | exact mu_certified source facts holds model ranked _ scope state valid ready (.inl selected)
                | exact mu_certified source facts holds model ranked _ scope state valid ready (.inr (.inl selected))
                | exact mu_certified source facts holds model ranked _ scope state valid ready (.inr (.inr selected))
                | exact left_union_certified source facts holds model ranked _ _ _ _ _ _ scope.leftAvailable state valid semantic
                | exact right_union_certified source facts holds model ranked _ _ _ _ _ _ scope.rightAvailable state valid semantic
                | exact SourceCurrentAllocatedNativeContextualReferenceCertificates.left_code source holds model ranked
                    _ scope.bindings _ _ state valid growth history
                | exact SourceCurrentAllocatedNativeContextualReferenceCertificates.right_code source holds model ranked
                    _ scope.bindings _ _ state valid growth history
                | exact compileRows_certified source facts holds model ranked _ _ _ _ _ _ _ _ _
                    scope.leftAvailable scope.rightAvailable state valid semantic
                | trivial

end MicroCFTA.SourceCurrentAllocatedNativeContextualNodeCertificates
