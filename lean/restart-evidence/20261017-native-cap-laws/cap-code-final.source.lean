import MicroCFTA.SourceCurrentConstrainedCapNativeScope
import MicroCFTA.SourceCurrentConstrainedCapNativeLaws
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceEqualityNativeCheckedCode

/-!
# Local finite-cap laws at actual native source continuations

The laws retain every common finite depth of the actual ordered operands.
The local source bindings retain their own Mu records. Primitive effects retain
their exact returned machines. This certificate does not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}

open SourceCurrentConstrainedCapNativeLaws (NodeLaw EdgeLaw)
open SourceCurrentConstrainedCap (Cap Edge)

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

/-- A literal node request uses its universal local law at the actual chosen depth. -/
theorem request_node (depth : Nat) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (left : Cap annotation depth request.left) (right : Cap annotation depth request.right) :
    Certified annotation source representation (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value) :=
  fun _ _ _ _ _ available law => ⟨available, law depth bindings left right⟩

/-- A literal row request uses its universal local law at the actual chosen depth. -/
theorem request_edge (depth : Nat) (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (left : Edge annotation depth request.left)
    (right : Edge annotation depth request.right) :
    Certified annotation source representation (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value) :=
  fun _ _ _ _ _ resident law => ⟨resident, law depth bindings left right⟩

/-- Literal edge work derives physical residence and the exact finite child depth. -/
theorem edge_work (depth : Nat) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (guardValid : depth = 0 → annotation guard)
    (bounded : ∀ value ∈ values, Cap annotation (depth - 1) value) :
    Certified annotation source representation (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeEdge annotation depth symbol guard values state.heap valid.1.coherent valid.1.cached
      available guardValid bounded⟩

/-- Literal node work derives its cap from the actual resident supplied rows. -/
theorem node_work (depth : Nat) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge)
    (bounded : ∀ edge ∈ edges, Edge annotation depth edge) :
    Certified annotation source representation (.work (makeNode edges) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.node_verified edges state.heap valid.1 resident).result _ _ rfl,
    SourceCurrentConstrainedCap.makeNode annotation depth edges state.heap valid.1.coherent valid.1.linked resident bounded⟩

/-- Literal union work retains the same cap across actual normalized members. -/
theorem union_work (depth : Nat) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value)
    (bounded : ∀ value ∈ values, Cap annotation depth value) :
    Certified annotation source representation (.work (makeUnion values) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.union_verified values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeUnion annotation depth values state.heap valid.1 available bounded⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeCode
