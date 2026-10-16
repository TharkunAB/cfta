import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds

/-!
# Local source certificates for causal request admission

Each recursive request carries its original scope and input admission.
Its continuation uses only physical returned-value facts.
Actual primitive returns determine the next certificate.
This predicate does not assume a completed recursive query.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
open Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeAdmissionCache
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable (source : InternedConstructorTemplates.State Symbol Guard)
  (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))

/-- Source requests establish admission before the native interpreter can publish them. -/
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
  | .node request next => NodeScope source request ∧ NodeCovered inputs request ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        Available after.heap value → Certified (next value) after post
  | .edge request next => EdgeScope source request ∧ EdgeCovered inputs request ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        EdgeResident after.heap value → Certified (next value) after post
  | .finishNode _ _ next | .finishEdge _ _ next => Certified next state post

/-- Local admission composes source continuations at their actual returned machine. -/
theorem certified_bind [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified source holds inputs code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      SemanticReady after.heap → intermediate after value → Certified source holds inputs (next value) after post) :
    Certified source holds inputs (code.bind next) state post := by
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
  | node request resume ih | edge request resume ih =>
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      intro value after afterValid growth afterSemantic available
      exact ih value after afterValid afterSemantic
        (certificate.2.2 value after afterValid growth afterSemantic available)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | finishNode handle value rest ih | finishEdge handle value rest ih =>
      exact ih state valid semantic certificate continuation

/-- A source node call derives its admission and resident-return continuation directly. -/
theorem requestNode_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (scope : NodeScope source request) (admitted : NodeCovered inputs request) :
    Certified source holds inputs (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value) :=
  ⟨scope, admitted, fun _ _ _ _ _ available => available⟩

/-- A source edge call retains both original row scopes and child admission. -/
theorem requestEdge_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (scope : EdgeScope source request) (admitted : EdgeCovered inputs request) :
    Certified source holds inputs (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value) :=
  ⟨scope, admitted, fun _ _ _ _ _ resident => resident⟩

/-- Ordered source calls retain admission and each returned physical output fact. -/
theorem walk_certified [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state →
      SemanticReady state.heap → input state request → Certified source holds inputs (call request) state output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (known : ∀ request ∈ requests, input state request) :
    Certified source holds inputs (walk call requests) state (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value absent; cases absent
  | cons first rest ih =>
      apply certified_bind source holds inputs _ _ state valid semantic output _
        (calls first List.mem_cons_self state valid semantic (known first List.mem_cons_self))
      intro value after afterValid growth afterSemantic available
      have tailKnown := fun request member => inputStable state after growth request
        (known request (List.mem_cons_of_mem _ member))
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member))
        after afterValid afterSemantic tailKnown
      apply certified_bind source holds inputs _ _ after afterValid afterSemantic _ _ tail
      intro values final _ later _ all
      intro found member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputStable after final later found available
      · exact all found member
end MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
