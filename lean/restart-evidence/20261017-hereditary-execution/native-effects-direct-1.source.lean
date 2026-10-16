import MicroCFTA.SourceCurrentHereditaryNativeCode
import MicroCFTA.SourceCurrentHereditaryConstruction

/-!
# Causal constructor effects at local native continuations

Ordinary Work preserves the conditional Mu store at its actual returned heap.
Optional binding derives that store from the current annotated body. Node and
edge requests retain their local input annotations and source bindings.
This certificate does not assume a completed prefix or a returned body law.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeEffects
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- Each literal Work job retains the conditional Mu store at its actual output heap. -/
def WorkSafe [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (job : Work Symbol Guard A) : Prop :=
  ∀ state, MuStored annotation state → MuStored annotation (run job state).2

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Pure Work changes no constructor record. -/
theorem WorkSafe.pure (annotation : Guard → Prop) (value : A) : WorkSafe annotation (.pure value : Work Symbol Guard A) :=
  fun _ stored => stored

/-- Ordered Work composes the actual intermediate constructor heaps. -/
theorem WorkSafe.bind {annotation : Guard → Prop} {job : Work Symbol Guard A} {next : A → Work Symbol Guard B}
    (first : WorkSafe annotation job) (later : ∀ value, WorkSafe annotation (next value)) : WorkSafe annotation (job.bind next) := by
  intro state stored
  simpa only [run_bind] using later (run job state).1 (run job state).2 (first state stored)

/-- Literal edge interning changes no complete Mu record. -/
theorem WorkSafe.makeEdge (annotation : Guard → Prop) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    WorkSafe annotation (makeEdge symbol guard values) := fun _ stored => stored.makeEdge symbol guard values

/-- Literal ordinary-node interning preserves all conditional Mu laws. -/
theorem WorkSafe.makeNode (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) :
    WorkSafe annotation (makeNode edges) := fun _ stored => stored.makeNode edges

/-- Literal union interning preserves all conditional Mu laws. -/
theorem WorkSafe.makeUnion (annotation : Guard → Prop) (values : List (Value Symbol Guard)) :
    WorkSafe annotation (makeUnion values) := fun _ stored => stored.makeUnion values

/-- Actual Work produces the representation premise needed by its continuation. -/
theorem work_stored (annotation : Guard → Prop) (job : Work Symbol Guard A) (safe : WorkSafe annotation job)
    (state : Machine Symbol Guard) (stored : MuStored annotation state.heap) (value : A) (after : Machine Symbol Guard)
    (done : work job state = .done value after) : MuStored annotation after.heap := by
  obtain ⟨rfl, rfl⟩ := work_done job state value after done
  exact safe state.heap stored

/-- Optional binding retains the exact stopping heap even when construction reports pending. -/
theorem optionalBinder_stored (annotation : Guard → Prop) (key : Nat × Nat) (body : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : MuStored annotation state.heap) (available : Available state.heap body) (annotated : Annotated annotation body) :
    MuStored annotation (construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state).state.heap := by
  have kept := (SourceCurrentHereditaryConstruction.optionalBinder annotation key body state.heap valid.1 available annotated stored).stored
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap <;>
    simpa only [actual, construction, Result.state, InternedNestedConstruction.Outcome.state] using kept

/-- An actual successful optional binder derives its returned annotation and conditional Mu store. -/
theorem optionalBinder_result (annotation : Guard → Prop) (key : Nat × Nat) (body : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : MuStored annotation state.heap) (available : Available state.heap body) (annotated : Annotated annotation body)
    (value : Value Symbol Guard) (after : Machine Symbol Guard)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after) :
    MuStored annotation after.heap ∧ Annotated annotation value := by
  have checked := SourceCurrentHereditaryConstruction.optionalBinder annotation key body state.heap valid.1 available annotated stored
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap with
  | pending => simp only [construction, actual] at done; cases done
  | done result heap =>
      simp only [construction, actual] at done
      cases done
      exact ⟨by simpa only [actual, InternedNestedConstruction.Outcome.state] using checked.stored, checked.result _ _ actual⟩

variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)

/-- Local source code carries primitive producers and its actual queried operand annotations. -/
def Certified (code : Code Symbol Guard A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => WorkSafe annotation job ∧ ∀ value after,
      work job state = .done value after → SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      MuStored annotation after.heap → Certified (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ Certified (next actual.1) after post
  | .read name next => Certified (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next => Available state.heap body ∧ Annotated annotation body ∧ ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → MuStored annotation after.heap → Certified (next value) after post
  | .node request next => Bindings annotation source request.domain.key ∧ Annotated annotation request.left ∧
      Annotated annotation request.right ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → MuStored annotation after.heap → Available after.heap value →
      NodeLaw annotation source request value → Certified (next value) after post
  | .edge request next => Bindings annotation source request.domain.key ∧ SourceCurrentHereditaryConstructors.Edge annotation request.left ∧
      SourceCurrentHereditaryConstructors.Edge annotation request.right ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → MuStored annotation after.heap → EdgeResident after.heap value →
      EdgeLaw annotation source request value → Certified (next value) after post
  | .finishNode .. | .finishEdge .. => False

/-- The companion certificate retains the older annotation contract unchanged. -/
theorem forget (code : Code Symbol Guard A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified annotation source code state post) :
    SourceCurrentHereditaryNativeCode.Certified annotation source (MuStored annotation) code state post := by
  induction code generalizing state with
  | pure | fail => exact certificate
  | work job next ih =>
      intro value after done valid growth stored
      exact ih value after (certificate.2 value after done valid growth stored)
  | enter domain left right first second next ih => exact ⟨certificate.1, certificate.2.1, ih _ _ certificate.2.2⟩
  | read name next ih => exact ih _ _ certificate
  | optionalBinder key body next ih =>
      intro value after done valid growth stored
      exact ih value after (certificate.2.2 value after done valid growth stored)
  | node request next ih | edge request next ih =>
      intro value after valid growth stored physical law
      exact ih value after (certificate.2.2.2 value after valid growth stored physical law)
  | finishNode | finishEdge => exact certificate

/-- Source sequencing uses each actual intermediate heap and produced representation. -/
theorem certified_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : MuStored annotation state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified annotation source code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      MuStored annotation after.heap → intermediate after value → Certified annotation source (next value) after post) :
    Certified annotation source (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl _) stored certificate
  | fail => trivial
  | work job resume ih =>
      refine ⟨certificate.1, ?_⟩
      intro value after done afterValid growth afterStored
      exact ih value after afterValid afterStored (certificate.2 value after done afterValid growth afterStored)
        (fun result final finalValid later finalStored middle => continuation result final finalValid (growth.trans later) finalStored middle)
  | optionalBinder key body resume ih =>
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      intro value after done afterValid growth afterStored
      exact ih value after afterValid afterStored (certificate.2.2 value after done afterValid growth afterStored)
        (fun result final finalValid later finalStored middle => continuation result final finalValid (growth.trans later) finalStored middle)
  | enter domain left right first second resume ih =>
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      exact ih _ _ certificate.1 stored certificate.2.2
        (fun result final finalValid later finalStored middle => continuation result final finalValid (certificate.2.1.trans later) finalStored middle)
  | read name resume ih => exact ih _ state valid stored certificate continuation
  | node request resume ih | edge request resume ih =>
      refine ⟨certificate.1, certificate.2.1, certificate.2.2.1, ?_⟩
      intro value after afterValid growth afterStored physical law
      exact ih value after afterValid afterStored (certificate.2.2.2 value after afterValid growth afterStored physical law)
        (fun result final finalValid later finalStored middle => continuation result final finalValid (growth.trans later) finalStored middle)
  | finishNode | finishEdge => cases certificate

/-- Ordered walks retain earlier outputs through the exact later heap extensions. -/
theorem certified_walk (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → MuStored annotation state.heap → input state request →
      Certified annotation source (call request) state output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : MuStored annotation state.heap)
    (inputs : ∀ request ∈ requests, input state request) :
    Certified annotation source (walk call requests) state (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value member; cases member
  | cons first rest ih =>
      apply certified_bind annotation source _ _ state valid stored output _
        (calls first List.mem_cons_self state valid stored (inputs first List.mem_cons_self))
      intro value after afterValid growth afterStored returned
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterValid afterStored
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      apply certified_bind annotation source _ _ after afterValid afterStored _ _ tail
      intro values final finalValid later finalStored all result member
      rcases List.mem_cons.mp member with rfl | present
      · exact outputStable after final later result returned
      · exact all result present

/-- Node requests expose their actual annotated operands before any recursive body. -/
theorem request_node (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key) (left : Annotated annotation request.left) (right : Annotated annotation request.right) :
    Certified annotation source (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value ∧ Annotated annotation value) :=
  ⟨bindings, left, right, fun _ _ _ _ _ available law => ⟨available, law bindings left right⟩⟩

/-- Edge requests expose both complete queried row annotations. -/
theorem request_edge (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left) (right : SourceCurrentHereditaryConstructors.Edge annotation request.right) :
    Certified annotation source (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) :=
  ⟨bindings, left, right, fun _ _ _ _ _ resident law => ⟨resident, law bindings left right⟩⟩

/-- Literal edge Work supplies both its representation producer and its local postcondition. -/
theorem edge_work (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (guardValid : annotation guard) (annotated : ∀ value ∈ values, Annotated annotation value) :
    Certified annotation source (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) :=
  ⟨WorkSafe.makeEdge annotation symbol guard values,
    SourceCurrentHereditaryNativeCode.edge_work annotation source (MuStored annotation) symbol guard values state valid available guardValid annotated⟩

/-- Literal node Work retains the Mu store and annotates its actual canonical result. -/
theorem node_work (edges : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge) (annotated : ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge annotation edge) :
    Certified annotation source (.work (makeNode edges) .pure) state (fun after value => Available after.heap value ∧ Annotated annotation value) :=
  ⟨WorkSafe.makeNode annotation edges, SourceCurrentHereditaryNativeCode.node_work annotation source (MuStored annotation) edges state valid resident annotated⟩

/-- Literal union Work retains the Mu store and annotates its actual canonical result. -/
theorem union_work (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (annotated : ∀ value ∈ values, Annotated annotation value) :
    Certified annotation source (.work (makeUnion values) .pure) state (fun after value => Available after.heap value ∧ Annotated annotation value) :=
  ⟨WorkSafe.makeUnion annotation values, SourceCurrentHereditaryNativeCode.union_work annotation source (MuStored annotation) values state valid available annotated⟩

/-- Optional binding exposes its current body inputs and derives its actual successful annotation. -/
theorem optional_binder_certified (key : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : MuStored annotation state.heap)
    (available : Available state.heap body) (annotated : Annotated annotation body) :
    Certified annotation source (.optionalBinder key body .pure) state (fun after value => Available after.heap value ∧ Annotated annotation value) := by
  refine ⟨available, annotated, ?_⟩
  intro value after done _ _ _
  have local := optionalBinder_result annotation key body state valid stored available annotated value after done
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap with
  | pending => simp only [construction, actual] at done; cases done
  | done result heap =>
      simp only [construction, actual] at done
      cases done
      exact ⟨(SourceRecursiveIntersectionMaybeMu.verified key body state.heap valid.1 available).result _ _ actual, local.2⟩

end MicroCFTA.SourceCurrentHereditaryNativeEffects
