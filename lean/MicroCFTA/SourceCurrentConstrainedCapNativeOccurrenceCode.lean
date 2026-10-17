import MicroCFTA.SourceCurrentConstrainedCapOriginalSupport
import MicroCFTA.SourceCurrentConstrainedCapNativeLaws
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceEqualityNativeCheckedCode

/-!
# Joint finite-cap and ranked laws at actual native continuations

Each literal request receives both local laws for its complete source inputs.
Primitive work derives the same cap and occurrence bounds at its actual
returned machine. Recursive completion and Mu winner readback remain separate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs edgeBudget)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE FreeBelow sourceWeight)
variable {Symbol Guard : Type}

open SourceCurrentConstrainedCapNativeOccurrenceCache (NodeLaw EdgeLaw)
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
      SourceCurrentConstrainedCapNativeLaws.NodeLaw annotation source request value →
      NodeLaw annotation source request value → Certified (next value) after post
  | .edge request next => ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → representation after.heap → EdgeResident after.heap value →
      SourceCurrentConstrainedCapNativeLaws.EdgeLaw annotation source request value →
      EdgeLaw annotation source request value → Certified (next value) after post
  | .finishNode .. | .finishEdge .. => False

/-- A larger bound retains free-name bounds and the coherent record's deep-name classification. -/
theorem classified_mono (weight : Reference → Nat) (first last : Nat) (value : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (available : Available state value) (known : Classified weight first value) (increase : first ≤ last) :
    Classified weight last value := by
  refine ⟨fun name member => Nat.le_trans (known.free name member) increase, ?_⟩
  intro name member
  rcases known.deep name member with smaller | zero
  · exact .inl (Nat.lt_of_lt_of_le smaller increase)
  · have free := known.free name (InternedDeepFreeNormalization.deep_free value state facts.coherent available name member)
    omega

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
      intro value after afterValid growth afterRepresented physical capLaw law
      exact ih value after afterValid afterRepresented (certificate value after afterValid growth afterRepresented physical capLaw law)
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

/-- A literal node request uses both local laws at its exact original pair rank. -/
theorem request_node (depth : Nat) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : NodeInputs source request)
    (left : Cap annotation depth request.left) (right : Cap annotation depth request.right) :
    Certified annotation source representation (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source)
          (SourceCurrentConstrainedCapNonplainRank.pairRank annotation request.left request.right) value) :=
  fun _ _ _ _ _ available capLaw law =>
    ⟨available, capLaw depth bindings.annotated left right, law depth bindings inputs left right⟩

/-- A literal row request uses both local laws at its exact zipped child budget. -/
theorem request_edge (depth : Nat) (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : EdgeInputs source request)
    (left : Edge annotation depth request.left) (right : Edge annotation depth request.right) :
    Certified annotation source representation (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value ∧
        ∀ child ∈ value.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) child) :=
  fun _ _ _ _ _ resident capLaw law =>
    ⟨resident, capLaw depth bindings.annotated left right, law depth bindings inputs left right⟩

/-- Literal edge work retains its actual ordered children's cap and free-name bounds. -/
theorem edge_work (depth bound : Nat) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (guardValid : depth = 0 → annotation guard)
    (bounded : ∀ value ∈ values, Cap annotation (depth - 1) value)
    (free : ∀ value ∈ values, FreeLE (sourceWeight annotation source) bound value) :
    Certified annotation source representation (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value ∧
        ∀ child ∈ value.children, FreeLE (sourceWeight annotation source) bound child) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  refine ⟨(InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeEdge annotation depth symbol guard values state.heap valid.1.coherent valid.1.cached
      available guardValid bounded, ?_⟩
  rw [InternedShallowValues.makeEdge_children symbol guard values state.heap valid.1.coherent valid.1.cached available]
  exact free

/-- Literal node work derives both laws from the actual resident rows and smaller child bounds. -/
theorem node_work (depth bound : Nat) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge)
    (bounded : ∀ edge ∈ edges, Edge annotation depth edge)
    (children : ∀ edge ∈ edges, ∀ value ∈ edge.children,
      FreeLE (sourceWeight annotation source) bound value ∧ FreeBelow (sourceWeight annotation source) bound value) :
    Certified annotation source representation (.work (makeNode edges) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.node_verified edges state.heap valid.1 resident).result _ _ rfl,
    SourceCurrentConstrainedCap.makeNode annotation depth edges state.heap valid.1.coherent valid.1.linked resident bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeNode _ bound edges state.heap valid.1 resident children⟩

/-- Literal union work retains both laws through actual normalized member readback. -/
theorem union_work (depth bound : Nat) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value)
    (bounded : ∀ value ∈ values, Cap annotation depth value)
    (classified : ∀ value ∈ values, Classified (sourceWeight annotation source) bound value)
    (normal : InternedStoredMuOrigins.Normal state.heap) :
    Certified annotation source representation (.work (makeUnion values) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.union_verified values state.heap valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeUnion annotation depth values state.heap valid.1 available bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeUnion _ bound values state.heap normal available classified⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCode
