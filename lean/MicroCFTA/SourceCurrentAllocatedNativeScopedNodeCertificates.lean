import MicroCFTA.SourceCurrentAllocatedNativeScopedCertificates
import MicroCFTA.SourceCurrentAllocatedNativeScopedMuCertificates

/-!
# Scope certificates for every actual source node branch

Each branch keeps only names from its incoming seen pairs. Mu code removes
the new pair after its child returns. Literal failures have no successful
result obligation. The certificate does not assert recursive completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeScopedNodeCertificates
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeScopedCode SourceCurrentAllocatedNativeScopedCertificates
open SourceRecursiveIntersectionResultScope (Scope)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The complete current source dispatcher derives result scope from exact child scopes. -/
theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap) (ready : NodeReady state request) :
    Certified (compileNode request) state (fun _ value => Scope request.domain.key.seen value) := by
  cases request with
  | mk domain left right =>
      cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
      | empty => simpa only [compileNode, selected] using empty_certified domain state
      | reset => simpa only [compileNode, selected] using reset_certified ⟨domain, left, right⟩ state
      | self => simpa only [compileNode, selected] using self_certified ⟨domain, left, right⟩ state selected
      | swap => simpa only [compileNode, selected] using swap_certified ⟨domain, left, right⟩ state
      | repeated pair => simpa only [compileNode, selected] using repeated_certified ⟨domain, left, right⟩ pair state selected
      | bothMu | leftMu | rightMu =>
          simpa only [compileNode, selected] using
            SourceCurrentAllocatedNativeScopedMuCertificates.mu_certified ⟨domain, left, right⟩ state valid ready
      | leftUnion =>
          cases left <;> simp only [compileNode, selected] <;> try trivial
          rename_i entry members depth free
          exact left_union_certified domain members right state valid semantic
      | rightUnion =>
          cases right <;> simp only [compileNode, selected] <;> try trivial
          rename_i entry members depth free
          exact right_union_certified domain members left state valid semantic
      | leftReference =>
          cases left <;> simp only [compileNode, selected] <;> try trivial
          rename_i name
          cases name <;> try trivial
          exact SourceCurrentAllocatedNativeScopedMuCertificates.left_reference domain _ right state
      | rightReference =>
          cases right <;> simp only [compileNode, selected] <;> try trivial
          rename_i name
          cases name <;> try trivial
          exact SourceCurrentAllocatedNativeScopedMuCertificates.right_reference domain _ left state
      | ordinary =>
          cases left <;> cases right <;> simp only [compileNode, selected] <;> try trivial
          exact compileRows_certified domain _ _ state valid semantic
      | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Certified]

end MicroCFTA.SourceCurrentAllocatedNativeScopedNodeCertificates
