import MicroCFTA.SourceCurrentHereditaryNativeScope
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceEqualityNativeCheckedCode

/-!
# Local hereditary laws at current native source continuations

The laws refer only to the queried operands and their bound source names.
Unrelated constrained records remain permitted. Primitive effects retain
their exact returned machines. This certificate does not assert completion.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}

/-- A node result retains annotations when its operands and source bindings carry them. -/
def NodeLaw (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Bindings valid source request.domain.key → Annotated valid request.left →
    Annotated valid request.right → Annotated valid value

/-- A row result retains its complete guard and actual child annotations. -/
def EdgeLaw (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard) : Prop :=
  Bindings valid source request.domain.key → SourceCurrentHereditaryConstructors.Edge valid request.left →
    SourceCurrentHereditaryConstructors.Edge valid request.right → SourceCurrentHereditaryConstructors.Edge valid value

variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
  (representation : InternedConstructorTemplates.State Symbol Guard → Prop)

/-- Each source continuation receives only the local law for its literal returned request. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after,
      SourceRecursiveIntersectionKernel.work job state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → representation after.heap → Certified (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ Certified (next actual.1) after post
  | .read name next => Certified (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → representation after.heap → Certified (next value) after post
  | .node request next => ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → representation after.heap → Available after.heap value →
      NodeLaw annotation source request value → Certified (next value) after post
  | .edge request next => ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → representation after.heap → EdgeResident after.heap value →
      EdgeLaw annotation source request value → Certified (next value) after post
  | .finishNode .. | .finishEdge .. => False

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Source sequencing composes local output laws through the actual returned machines. -/
theorem certified_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified annotation source representation code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      representation after.heap → intermediate after value → Certified annotation source representation (next value) after post) :
    Certified annotation source representation (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl _) represented certificate
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after done afterValid growth afterRepresented
      exact ih value after afterValid afterRepresented (certificate value after done afterValid growth afterRepresented)
        (fun result final finalValid later finalRepresented middle => continuation result final finalValid (growth.trans later) finalRepresented middle)
  | enter domain left right first second resume ih =>
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      exact ih _ _ certificate.1 represented certificate.2.2
        (fun result final finalValid later finalRepresented middle => continuation result final finalValid (certificate.2.1.trans later) finalRepresented middle)
  | read name resume ih => exact ih _ state valid represented certificate continuation
  | node request resume ih | edge request resume ih =>
      intro value after afterValid growth afterRepresented physical law
      exact ih value after afterValid afterRepresented (certificate value after afterValid growth afterRepresented physical law)
        (fun result final finalValid later finalRepresented middle => continuation result final finalValid (growth.trans later) finalRepresented middle)
  | finishNode | finishEdge => cases certificate

/-- Ordered source walks retain each earlier output after every later physical effect. -/
theorem certified_walk (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → representation state.heap → input state request →
      Certified annotation source representation (call request) state output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap)
    (inputs : ∀ request ∈ requests, input state request) :
    Certified annotation source representation (walk call requests) state (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value member; cases member
  | cons first rest ih =>
      apply certified_bind annotation source representation _ _ state valid represented output _
        (calls first List.mem_cons_self state valid represented (inputs first List.mem_cons_self))
      intro value after afterValid growth afterRepresented returned
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterValid afterRepresented
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      apply certified_bind annotation source representation _ _ after afterValid afterRepresented _ _ tail
      intro values final finalValid later finalRepresented all result member
      rcases List.mem_cons.mp member with rfl | present
      · exact outputStable after final later result returned
      · exact all result present

/-- A literal node request uses its own conditional result law. -/
theorem request_node (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (left : Annotated annotation request.left) (right : Annotated annotation request.right) :
    Certified annotation source representation (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) :=
  fun _ _ _ _ _ available law => ⟨available, law bindings left right⟩

/-- A literal row request uses its own complete guard and child result law. -/
theorem request_edge (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left)
    (right : SourceCurrentHereditaryConstructors.Edge annotation request.right) :
    Certified annotation source representation (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) :=
  fun _ _ _ _ _ resident law => ⟨resident, law bindings left right⟩

/-- Literal edge work derives both physical residence and its local annotation. -/
theorem edge_work (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (guardValid : annotation guard)
    (annotated : ∀ value ∈ values, Annotated annotation value) :
    Certified annotation source representation (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentHereditaryConstructors.makeEdge annotation symbol guard values state.heap valid.1.coherent valid.1.cached
      available guardValid annotated⟩

/-- Literal node work derives its annotation from the actual supplied resident rows. -/
theorem node_work (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge)
    (annotated : ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge annotation edge) :
    Certified annotation source representation (.work (makeNode edges) .pure) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.node_verified edges state.heap valid.1 resident).result _ _ rfl,
    SourceCurrentHereditaryConstructors.makeNode annotation edges state.heap valid.1.coherent valid.1.linked resident annotated⟩

/-- Literal union work retains only the supplied annotated members. -/
theorem union_work (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value)
    (annotated : ∀ value ∈ values, Annotated annotation value) :
    Certified annotation source representation (.work (makeUnion values) .pure) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.union_verified values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentHereditaryConstructors.makeUnion annotation values state.heap valid.1 available annotated⟩

end MicroCFTA.SourceCurrentHereditaryNativeCode
