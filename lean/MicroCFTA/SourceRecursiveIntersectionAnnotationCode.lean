import MicroCFTA.SourceRecursiveIntersectionCodeSemantic
import MicroCFTA.SourceEqualityAnnotationStoredSyntax

/-!
# Annotation conditions at actual native source continuations

The certificate checks actual emitted work and available optional binder
bodies. Recursive continuations retain their returned physical cache scope.
Source safety supplies readiness independently of annotation preservation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionAnnotationCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationHeap (Heap)

/-- Source code checks annotation preservation at its actual effect and request sites. -/
def Certified (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work job next =>
      let actual := SourceRecursiveIntersectionKernel.work job state
      (Heap annotation state.heap → Heap annotation actual.state.heap) ∧
        ∀ value after, actual = .done value after → Certified annotation (next value) after
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      Certified annotation (next actual.1) {state with domains := actual.2}
  | .read name next => Certified annotation (next (SourcePreparedSharedRows.read state.heap name)) state
  | .optionalBinder key body next =>
      Available state.heap body ∧
        ∀ value after, construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
          Certified annotation (next value) after
  | .node request next =>
      NodeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → Certified annotation (next value) after
  | .edge request next =>
      EdgeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → Certified annotation (next value) after
  | .finishNode _ _ next | .finishEdge _ _ next => Certified annotation next state

/-- Safe source sequencing retains annotation conditions through exact returned machines. -/
theorem annotation_bind (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (intermediate : Machine Symbol Guard → A → Prop)
    (safe : Safe code state intermediate) (semantic : Certified annotation code state)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → Certified annotation (next value) after) : Certified annotation (code.bind next) state := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl state) safe
  | fail failure => exact semantic
  | work job resume ih | optionalBinder key body resume ih =>
      refine ⟨semantic.1, ?_⟩
      intro value after done
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [done, Result.state] using safe.1
      have growth : Extension state after := by simpa only [done, Result.state] using safe.2.1
      exact ih value after afterValid (safe.2.2 value after done) (semantic.2 value after done)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | enter domain left right first second resume ih =>
      exact ih _ _ safe.1 safe.2.2 semantic
        (fun result final finalValid later property => continuation result final finalValid (safe.2.1.trans later) property)
  | read name resume ih => exact ih _ state valid safe semantic continuation
  | node request resume ih | edge request resume ih =>
      refine ⟨semantic.1, ?_⟩
      intro value after afterValid growth available
      exact ih value after afterValid (safe.2 value after afterValid growth available) (semantic.2 value after afterValid growth available)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | finishNode | finishEdge => cases safe

/-- Ordered safe source walks retain annotation conditions after every actual earlier child effect. -/
theorem annotation_walk (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (safeCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Safe (call request) state output)
    (semanticCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Certified annotation (call request) state)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request) :
    Certified annotation (walk call requests) state := by
  induction requests generalizing state with
  | nil => trivial
  | cons first rest ih =>
      apply annotation_bind annotation _ _ state valid output
        (safeCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
        (semanticCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
      intro value after afterValid growth available
      have tailInputs := fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member))
      have tailSafe := safe_walk call rest input output inputStable outputStable
        (fun request member => safeCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      have tailSemantic := ih (fun request member => safeCalls request (List.mem_cons_of_mem _ member))
        (fun request member => semanticCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      exact annotation_bind annotation _ _ after afterValid _ tailSafe tailSemantic (fun _ _ _ _ _ => trivial)

/-- An available node request retains annotation conditions through every physical returned value. -/
theorem annotation_requestNode (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard) (ready : NodeReady state ⟨domain, left, right⟩) :
    Certified annotation (requestNode domain left right) state := ⟨ready, fun _ _ _ _ _ => trivial⟩

/-- A resident row request retains annotation conditions through every physical returned row. -/
theorem annotation_requestEdge (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (ready : EdgeReady state ⟨domain, left, right⟩) :
    Certified annotation (requestEdge domain left right) state := ⟨ready, fun _ _ _ _ _ => trivial⟩

/-- Literal source edge work preserves the heap from its exact emitted guard check. -/
theorem annotation_edge [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (valid : annotation guard) :
    Certified annotation (.work (makeEdge symbol guard values) .pure) state :=
  ⟨fun heap => SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeEdge annotation symbol guard values valid) state.heap heap,
    fun _ _ _ => trivial⟩

/-- Actual ordinary-node work retains every physical edge annotation. -/
theorem annotation_node [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) : Certified annotation (.work (makeNode edges) .pure) state :=
  ⟨fun heap => SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation edges) state.heap heap, fun _ _ _ => trivial⟩

/-- Actual union work retains every physical edge annotation. -/
theorem annotation_union [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) : Certified annotation (.work (makeUnion values) .pure) state :=
  ⟨fun heap => SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeUnion annotation values) state.heap heap, fun _ _ _ => trivial⟩

/-- The actual optional-binder instruction retains its available original source body. -/
theorem annotation_optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (key : Nat × Nat) (body : Value Symbol Guard)
    (state : Machine Symbol Guard) (available : Available state.heap body) :
    Certified annotation (.optionalBinder key body .pure) state := ⟨available, fun _ _ _ => trivial⟩

end MicroCFTA.SourceRecursiveIntersectionAnnotationCode
