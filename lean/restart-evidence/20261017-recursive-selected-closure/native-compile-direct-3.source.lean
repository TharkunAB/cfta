import MicroCFTA.SourceCurrentHereditaryNativeCode
import MicroCFTA.SourceCurrentHereditaryConstruction

/-!
# Local annotation certificates for actual native node compilation

The compiler retains the actual source bindings, rows, and union members.
Optional binding uses an explicit local constructor law. That law needs a
causal warm constructor invariant. Physical validity alone does not imply it.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeCompile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryNativeCode
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}
variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
  (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The local binder law concerns one actual primitive return in a represented heap. -/
def Binders : Prop := ∀ key body state, Facts state → representation state → Available state body →
  Annotated annotation body → ∀ value after,
    SourceRecursiveIntersectionMaybeMu.maybeMu key body state = .done value after → Annotated annotation value

/-- Actual constructor history supplies the binder law from its causal Mu store. -/
theorem causal_binders : Binders annotation (SourceCurrentHereditaryConstruction.MuStored annotation) := by
  intro key body state facts stored available annotated value after done
  exact (SourceCurrentHereditaryConstruction.optionalBinder annotation key body state facts available annotated stored).result value after done

/-- Literal hash-joined rows retain their own guards and child annotations. -/
theorem rows_certified [DecidableEq Symbol] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key)
    (leftAnnotated : ∀ edge ∈ left, SourceCurrentHereditaryConstructors.Edge annotation edge)
    (rightAnnotated : ∀ edge ∈ right, SourceCurrentHereditaryConstructors.Edge annotation edge) :
    Certified annotation source representation (compileRows domain left right) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  let input := fun (_ : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    SourceCurrentHereditaryConstructors.Edge annotation pair.1 ∧ SourceCurrentHereditaryConstructors.Edge annotation pair.2
  let output := fun (after : Machine Symbol Guard) (edge : EdgeValue Symbol Guard) =>
    EdgeResident after.heap edge ∧ SourceCurrentHereditaryConstructors.Edge annotation edge
  have walked := certified_walk annotation source representation
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs left right) input output (by intro _ _ _ _ known; exact known)
    (by intro before after growth edge known; exact ⟨edge_stable before after growth edge known.1, known.2⟩)
    (by intro pair _ current _ _ known; exact request_edge annotation source representation ⟨domain, pair.1, pair.2⟩ current bindings known.1 known.2)
    state valid represented (by
      intro pair member
      have inside := (pairs_member left right pair).mp member
      exact ⟨leftAnnotated pair.1 inside.1, rightAnnotated pair.2 inside.2.1⟩)
  unfold compileRows
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact node_work annotation source representation values after afterValid
    (fun edge member => (returned edge member).1) (fun edge member => (returned edge member).2)

/-- Each left union callback retains its literal member and original right operand. -/
theorem left_union_certified (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key)
    (membersAnnotated : ∀ value ∈ members, Annotated annotation value) (rightAnnotated : Annotated annotation right) :
    Certified annotation source representation
      ((walk (fun member => requestNode domain member right) members).bind fun values => .work (makeUnion values) .pure)
      state (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  have walked := certified_walk annotation source representation
    (fun member => requestNode domain member right) members (fun _ value => Annotated annotation value)
    (fun after value => Available after.heap value ∧ Annotated annotation value)
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by intro value _ current _ _ known; exact request_node annotation source representation ⟨domain, value, right⟩ current bindings known rightAnnotated)
    state valid represented membersAnnotated
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact union_work annotation source representation values after afterValid
    (fun value member => (returned value member).1) (fun value member => (returned value member).2)

/-- Each right union callback retains the original left operand and literal member. -/
theorem right_union_certified (domain : Interned DomainKey) (left : Value Symbol Guard)
    (members : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key) (leftAnnotated : Annotated annotation left)
    (membersAnnotated : ∀ value ∈ members, Annotated annotation value) :
    Certified annotation source representation
      ((walk (fun member => requestNode domain left member) members).bind fun values => .work (makeUnion values) .pure)
      state (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  have walked := certified_walk annotation source representation
    (fun member => requestNode domain left member) members (fun _ value => Annotated annotation value)
    (fun after value => Available after.heap value ∧ Annotated annotation value)
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by intro value _ current _ _ known; exact request_node annotation source representation ⟨domain, left, value⟩ current bindings leftAnnotated known)
    state valid represented membersAnnotated
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact union_work annotation source representation values after afterValid
    (fun value member => (returned value member).1) (fun value member => (returned value member).2)

/-- Actual optional binding uses the represented local constructor law at its incoming heap. -/
theorem optional_binder_certified (binders : Binders annotation representation) (key : Nat × Nat)
    (body : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (available : Available state.heap body) (annotated : Annotated annotation body) :
    Certified annotation source representation (.optionalBinder key body .pure) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  intro value after done _ _ _
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap with
  | pending => simp only [construction, actual] at done; cases done
  | done result heap =>
      simp only [construction, actual] at done
      cases done
      exact ⟨(SourceRecursiveIntersectionMaybeMu.verified key body state.heap valid.1 available).result _ _ actual,
        binders key body state.heap valid.1 represented available annotated _ _ actual⟩

/-- Actual Mu entry retains the encountered bindings before the stored-body callback. -/
theorem mu_certified (binders : Binders annotation representation) (request : NodeRequest Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftAnnotated : Annotated annotation request.left) (rightAnnotated : Annotated annotation request.right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : NodeReady state request) :
    Certified annotation source representation (compileMu request.domain request.left request.right) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  cases first : SourceRecursiveIntersectionControl.identity request.left <;>
    cases second : SourceRecursiveIntersectionControl.identity request.right <;>
    simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstName secondName
  have entered := SourceRecursiveIntersectionKernel.entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 firstName secondName
  have enteredBindings := bindings.enter annotation source request.domain.key request.left request.right
    leftAvailable rightAvailable leftAnnotated rightAnnotated state.domains valid.2 firstName secondName
  refine ⟨entered.1, entered.2.1, ?_⟩
  intro value after afterValid growth represented available law
  exact optional_binder_certified annotation source representation binders _ value after afterValid represented available
    (law enteredBindings (SourceCurrentHereditaryNativeScope.body_annotated annotation _ leftAnnotated)
      (SourceCurrentHereditaryNativeScope.body_annotated annotation _ rightAnnotated))

/-- A literal bound-name read retains its annotated original Mu after legitimate heap growth. -/
theorem reference_certified (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (bindings : Bindings annotation source domain.key) (annotated : Annotated annotation other)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified annotation source representation (compileReference domain name other left) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  unfold compileReference
  split
  · rename_i member
    obtain ⟨bound, found, _, _, _, boundAnnotated⟩ :=
      bindings.read annotation source state.heap valid.1 growth history domain.key name member
    simp only [Certified, found]
    cases left
    · exact request_node annotation source representation ⟨domain, other, bound⟩ state bindings annotated boundAnnotated
    · exact request_node annotation source representation ⟨domain, bound, other⟩ state bindings boundAnnotated annotated
  · trivial

/-- Every literal node branch derives local output annotations from its represented binder law. -/
theorem node_certified [DecidableEq Symbol] (binders : Binders annotation representation)
    (request : NodeRequest Symbol Guard) (bindings : Bindings annotation source request.domain.key)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftAnnotated : Annotated annotation request.left) (rightAnnotated : Annotated annotation request.right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified annotation source representation (compileNode request) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  cases request with
  | mk domain left right =>
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simpa only [compileNode, selected, Certified] using And.intro (empty_available state.heap) (Annotated.empty (valid := annotation))
    | reset =>
        simpa only [compileNode, selected] using request_node annotation source representation ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state
          (SourceCurrentHereditaryNativeScope.empty annotation source) leftAnnotated rightAnnotated
    | self => simpa only [compileNode, selected, Certified] using And.intro ready.2.1 leftAnnotated
    | swap => simpa only [compileNode, selected] using request_node annotation source representation ⟨domain, right, left⟩ state bindings rightAnnotated leftAnnotated
    | repeated key =>
        simp only [compileNode, selected, Certified, SourceRecursiveIntersectionControl.repeatedValue]
        exact ⟨reference_available state.heap _ (by intro name member; simp [Value.free] at member), .reference _⟩
    | bothMu | leftMu | rightMu =>
        simpa only [compileNode, selected] using mu_certified annotation source representation binders _ bindings
          leftAvailable rightAvailable leftAnnotated rightAnnotated state valid ready
    | leftUnion =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        cases leftAnnotated with
        | union entry members depth free children =>
            exact left_union_certified annotation source representation domain _ right state valid represented bindings children rightAnnotated
    | rightUnion =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        cases rightAnnotated with
        | union entry members depth free children =>
            exact right_union_certified annotation source representation domain left _ state valid represented bindings leftAnnotated children
    | leftReference =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        rename_i name
        cases name <;> first
          | exact reference_certified annotation source representation _ _ _ true bindings rightAnnotated state valid growth history
          | trivial
    | rightReference =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        rename_i name
        cases name <;> first
          | exact reference_certified annotation source representation _ _ _ false bindings leftAnnotated state valid growth history
          | trivial
    | ordinary =>
        simp only [compileNode, selected]
        cases left <;> cases right <;> try trivial
        apply rows_certified annotation source representation _ _ _ state valid represented bindings
        · intro edge member; exact SourceCurrentHereditaryConstructors.node_edge leftAnnotated edge member
        · intro edge member; exact SourceCurrentHereditaryConstructors.node_edge rightAnnotated edge member
    | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Certified]

/-- The causal constructor invariant discharges the local binder premise for every node branch. -/
theorem node_with_store [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (bindings : Bindings annotation source request.domain.key)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftAnnotated : Annotated annotation request.left) (rightAnnotated : Annotated annotation request.right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : SourceCurrentHereditaryConstruction.MuStored annotation state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified annotation source (SourceCurrentHereditaryConstruction.MuStored annotation) (compileNode request) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) :=
  node_certified annotation source _ (causal_binders annotation) request bindings leftAvailable rightAvailable
    leftAnnotated rightAnnotated state valid stored ready growth history

end MicroCFTA.SourceCurrentHereditaryNativeCompile
