import MicroCFTA.SourceRecursiveIntersectionCompileSafety
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Semantic heap conditions for actual source continuations

The certificate retains primitive heap preservation and available optional
binder inputs. Recursive continuations accept actual available results after
valid source growth. Native completion frames add no heap effect.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Source code retains the semantic heap conditions at its actual effect and request sites. -/
def Semantic [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work job next =>
      let actual := SourceRecursiveIntersectionKernel.work job state
      (SemanticHeap state.heap → SemanticHeap actual.state.heap) ∧
        ∀ value after, actual = .done value after → Semantic (next value) after
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      Semantic (next actual.1) {state with domains := actual.2}
  | .read name next => Semantic (next (SourcePreparedSharedRows.read state.heap name)) state
  | .optionalBinder key body next =>
      Available state.heap body ∧
        ∀ value after, construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
          Semantic (next value) after
  | .node request next =>
      NodeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → Semantic (next value) after
  | .edge request next =>
      EdgeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → Semantic (next value) after
  | .finishNode _ _ next | .finishEdge _ _ next => Semantic next state

/-- Safe source sequencing retains the semantic heap conditions through exact returned machines. -/
theorem semantic_bind [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (intermediate : Machine Symbol Guard → A → Prop)
    (safe : Safe code state intermediate) (semantic : Semantic code state)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → Semantic (next value) after) : Semantic (code.bind next) state := by
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

/-- Ordered safe source walks retain the semantic heap conditions after every actual earlier child effect. -/
theorem semantic_walk [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (safeCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Safe (call request) state output)
    (semanticCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Semantic (call request) state)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request) :
    Semantic (walk call requests) state := by
  induction requests generalizing state with
  | nil => trivial
  | cons first rest ih =>
      apply semantic_bind _ _ state valid output
        (safeCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
        (semanticCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
      intro value after afterValid growth available
      have tailInputs := fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member))
      have tailSafe := safe_walk call rest input output inputStable outputStable
        (fun request member => safeCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      have tailSemantic := ih (fun request member => safeCalls request (List.mem_cons_of_mem _ member))
        (fun request member => semanticCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      exact semantic_bind _ _ after afterValid _ tailSafe tailSemantic (fun _ _ _ _ _ => trivial)

/-- An available node request retains semantic conditions through every physical returned value. -/
theorem semantic_requestNode [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard) (ready : NodeReady state ⟨domain, left, right⟩) :
    Semantic (requestNode domain left right) state := ⟨ready, fun _ _ _ _ _ => trivial⟩

/-- A resident row request retains semantic conditions through every physical returned row. -/
theorem semantic_requestEdge [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (ready : EdgeReady state ⟨domain, left, right⟩) :
    Semantic (requestEdge domain left right) state := ⟨ready, fun _ _ _ _ _ => trivial⟩

/-- Emitted edge work derives its semantic heap preservation from its actual available children. -/
theorem semantic_edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (available : ∀ value ∈ values, Available state.heap value) :
    Semantic (.work (makeEdge symbol guard values) .pure) state :=
  ⟨fun semantic => SourceRecursiveIntersectionSemanticHeap.edge symbol guard values state.heap semantic available,
    fun _ _ _ => trivial⟩

/-- Emitted node work derives its semantic heap preservation from its actual resident rows. -/
theorem semantic_node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (resident : ∀ edge ∈ edges, EdgeResident state.heap edge) :
    Semantic (.work (makeNode edges) .pure) state :=
  ⟨fun semantic => SourceRecursiveIntersectionSemanticHeap.node edges state.heap semantic resident, fun _ _ _ => trivial⟩

/-- Emitted union work derives its semantic heap preservation from its actual available operands. -/
theorem semantic_union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (available : ∀ value ∈ values, Available state.heap value) :
    Semantic (.work (makeUnion values) .pure) state :=
  ⟨fun semantic => SourceRecursiveIntersectionSemanticHeap.union values state.heap semantic available, fun _ _ _ => trivial⟩

/-- An actual optional-binder instruction retains its available body at the source site. -/
theorem semantic_optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : Machine Symbol Guard) (available : Available state.heap body) :
    Semantic (.optionalBinder key body .pure) state := ⟨available, fun _ _ _ => trivial⟩

end MicroCFTA.SourceRecursiveIntersectionCode
