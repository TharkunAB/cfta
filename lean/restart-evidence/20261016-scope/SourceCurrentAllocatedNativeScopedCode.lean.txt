import MicroCFTA.SourceRecursiveIntersectionResultScope
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Local scope certificates for source code

Each recursive continuation receives the scope for its exact request.
Primitive continuations retain the actual returned machine. This local
predicate does not execute a request or assert a completed native result.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeScopedCode
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionResultScope
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Local continuation scopes use actual primitive returns and exact child requests. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after,
      SourceRecursiveIntersectionKernel.work job state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Certified (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ Certified (next actual.1) after post
  | .read name next => Certified (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Certified (next value) after post
  | .node request next => ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Available after.heap value → Scope request.domain.key.seen value →
      Certified (next value) after post
  | .edge request next => ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      EdgeResident after.heap value → EdgeScope request.domain.key.seen value →
      Certified (next value) after post
  | .finishNode .. | .finishEdge .. => False

/-- Local scope certification composes source continuations and actual growth. -/
theorem certified_bind [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      SemanticReady after.heap → intermediate after value → Certified (next value) after post) :
    Certified (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl _) semantic certificate
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after done afterValid growth afterSemantic
      exact ih value after afterValid afterSemantic
        (certificate value after done afterValid growth afterSemantic)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | enter domain left right first second resume ih =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      exact ih actual.1 after certificate.1 semantic certificate.2.2
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (certificate.2.1.trans later) finalSemantic middle)
  | read name resume ih => exact ih _ state valid semantic certificate continuation
  | node request resume ih =>
      intro value after afterValid growth afterSemantic available law
      exact ih value after afterValid afterSemantic
        (certificate value after afterValid growth afterSemantic available law)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | edge request resume ih =>
      intro value after afterValid growth afterSemantic resident law
      exact ih value after afterValid afterSemantic
        (certificate value after afterValid growth afterSemantic resident law)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | finishNode | finishEdge => cases certificate

end MicroCFTA.SourceCurrentAllocatedNativeScopedCode
