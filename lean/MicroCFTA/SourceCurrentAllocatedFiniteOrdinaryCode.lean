import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

/-!
# Structural continuation certificates for current source code

Each recursive request retains its ordered operands and empty seen list.
Its continuation uses the structural certificate for that exact request.
Primitive continuations use their actual physical inputs and returned heap.
These local certificates do not assert native execution or termination.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored (NodeCertificate EdgeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "EdgeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge

/-- A structural node request starts outside recursive binder traversal. -/
def NodeInputs (request : NodeRequest Symbol Guard) : Prop :=
  request.domain.key.seen = [] ∧ NodeDomain request.left ∧ NodeDomain request.right

/-- A structural edge request retains both complete finite ordinary forests. -/
def EdgeInputs (request : EdgeRequest Symbol Guard) : Prop :=
  request.domain.key.seen = [] ∧ EdgeDomain request.left ∧ EdgeDomain request.right

/-- Local certificates admit only source instructions in the finite ordinary fragment. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after,
      SourceRecursiveIntersectionKernel.work job state = .done value after →
      SourceEqualityNativeDemandHeapPrimitives.WorkInputs state.heap job →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Certified (next value) after post
  | .node request next => NodeInputs request ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Available after.heap value → NodeCertificate request value → Certified (next value) after post
  | .edge request next => EdgeInputs request ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      EdgeResident after.heap value → EdgeCertificate request value → Certified (next value) after post
  | .enter .. | .read .. | .optionalBinder .. | .finishNode .. | .finishEdge .. => False

/-- Structural certificates compose at the actual returned machines. -/
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
  | work job resume ih =>
      intro value after done inputs afterValid growth afterSemantic
      exact ih value after afterValid afterSemantic
        (certificate value after done inputs afterValid growth afterSemantic)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | node request resume ih | edge request resume ih =>
      refine ⟨certificate.1, ?_⟩
      intro value after afterValid growth afterSemantic available law
      exact ih value after afterValid afterSemantic
        (certificate.2 value after afterValid growth afterSemantic available law)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | enter | read | optionalBinder | finishNode | finishEdge => cases certificate

/-- A literal node instruction passes its own result certificate to its continuation. -/
theorem request_node [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) (inputs : NodeInputs request) :
    Certified (requestNode request.domain request.left request.right) state
      (fun _ value => NodeCertificate request value) :=
  ⟨inputs, fun _ _ _ _ _ _ law => law⟩

/-- A literal edge instruction passes its own result certificate to its continuation. -/
theorem request_edge [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) (inputs : EdgeInputs request) :
    Certified (requestEdge request.domain request.left request.right) state
      (fun _ value => EdgeCertificate request value) :=
  ⟨inputs, fun _ _ _ _ _ _ law => law⟩

/-- Ordered local calls retain the certificate for every original occurrence. -/
theorem certified_walk [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (values : List A) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (law : A → B → Prop)
    (calls : ∀ input ∈ values, ∀ after, SourceRecursiveIntersectionKernel.Valid after →
      Extension state after → SemanticReady after.heap → Certified (call input) after (fun _ output => law input output)) :
    Certified (walk call values) state (fun _ outputs => Language.All₂ law values outputs) := by
  induction values generalizing state with
  | nil => exact .nil
  | cons first rest ih =>
      apply certified_bind (call first) _ state valid semantic (fun _ output => law first output)
      · exact calls first List.mem_cons_self state valid (.refl _) semantic
      · intro output middle middleValid growth middleSemantic firstLaw
        apply certified_bind (walk call rest) _ middle middleValid middleSemantic
          (fun _ outputs => Language.All₂ law rest outputs)
        · exact ih middle middleValid middleSemantic (fun input member after afterValid later afterSemantic =>
            calls input (List.mem_cons_of_mem _ member) after afterValid (growth.trans later) afterSemantic)
        · intro outputs final _ _ _ restLaw
          exact .cons firstLaw restLaw

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode
