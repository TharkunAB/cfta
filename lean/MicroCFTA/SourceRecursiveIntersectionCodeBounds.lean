import MicroCFTA.SourceRecursiveIntersectionRequestScope

/-!
# Request bounds through source code and continuations

Every recursive request retains original input scope and a least successful
semantic bound below the current body limit. Explicit source failures are
excluded. Actual effects use their exact returned machines. Recursive
continuations accept available returned values
after valid source growth. No completed execution is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- A recursive node request retains original scope and strictly decreases the current body limit. -/
def NodeBelow [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (request : NodeRequest Symbol Guard) : Prop :=
  NodeScope source request ∧ ∃ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete < bound

/-- A recursive row request retains original scope and strictly decreases the current body limit. -/
def EdgeBelow [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (request : EdgeRequest Symbol Guard) : Prop :=
  EdgeScope source request ∧ ∃ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete < bound

/-- Source code excludes failures and retains original request scope and its strict body limit through actual continuations. -/
def Below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Prop :=
  match code with
  | .pure _ => True
  | .fail _ => False
  | .work job next =>
      let actual := SourceRecursiveIntersectionKernel.work job state
      ∀ value after, actual = .done value after → Below source holds bound (next value) after
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      Below source holds bound (next actual.1) {state with domains := actual.2}
  | .read name next => Below source holds bound (next (SourcePreparedSharedRows.read state.heap name)) state
  | .optionalBinder key body next =>
      let actual := construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state
      ∀ value after, actual = .done value after → Below source holds bound (next value) after
  | .node request next =>
      NodeBelow source holds bound request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → Below source holds bound (next value) after
  | .edge request next =>
      EdgeBelow source holds bound request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → Below source holds bound (next value) after
  | .finishNode .. | .finishEdge .. => False

/-- Safe source sequencing retains the strict request limit through exact returned machines. -/
theorem below_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (intermediate : Machine Symbol Guard → A → Prop)
    (safe : Safe code state intermediate) (bounded : Below source holds bound code state)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → Below source holds bound (next value) after) : Below source holds bound (code.bind next) state := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl state) safe
  | fail failure => exact bounded
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after done
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [done, Result.state] using safe.1
      have growth : Extension state after := by simpa only [done, Result.state] using safe.2.1
      exact ih value after afterValid (safe.2.2 value after done) (bounded value after done)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | enter domain left right first second resume ih =>
      exact ih _ _ safe.1 safe.2.2 bounded
        (fun result final finalValid later property => continuation result final finalValid (safe.2.1.trans later) property)
  | read name resume ih => exact ih _ state valid safe bounded continuation
  | node request resume ih | edge request resume ih =>
      refine ⟨bounded.1, ?_⟩
      intro value after afterValid growth available
      exact ih value after afterValid (safe.2 value after afterValid growth available) (bounded.2 value after afterValid growth available)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | finishNode | finishEdge => cases bounded

/-- Ordered safe source walks retain the strict request limit after every actual earlier child effect. -/
theorem below_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (safeCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Safe (call request) state output)
    (belowCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Below source holds bound (call request) state)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request) :
    Below source holds bound (walk call requests) state := by
  induction requests generalizing state with
  | nil => trivial
  | cons first rest ih =>
      apply below_bind source holds bound _ _ state valid output
        (safeCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
        (belowCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
      intro value after afterValid growth available
      have tailInputs := fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member))
      have tailSafe := safe_walk call rest input output inputStable outputStable
        (fun request member => safeCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      have tailBelow := ih (fun request member => safeCalls request (List.mem_cons_of_mem _ member))
        (fun request member => belowCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      exact below_bind source holds bound _ _ after afterValid _ tailSafe tailBelow (fun _ _ _ _ _ => trivial)

/-- A complete physical work instruction adds no recursive request. -/
theorem below_work [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (job : Work Symbol Guard A) (state : Machine Symbol Guard) :
    Below source holds bound (.work job .pure) state := fun _ _ _ => trivial

/-- An optional-binder instruction adds no outer recursive intersection request. -/
theorem below_optionalBinder [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (key : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard) :
    Below source holds bound (.optionalBinder key body .pure) state := fun _ _ _ => trivial

/-- A checked original node request retains its limit through every available returned value. -/
theorem below_requestNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bounded : NodeBelow source holds bound request) : Below source holds bound (requestNode request.domain request.left request.right) state :=
  ⟨bounded, fun _ _ _ _ _ => trivial⟩

/-- A checked original row request retains its limit through every resident returned row. -/
theorem below_requestEdge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bounded : EdgeBelow source holds bound request) : Below source holds bound (requestEdge request.domain request.left request.right) state :=
  ⟨bounded, fun _ _ _ _ _ => trivial⟩

end MicroCFTA.SourceRecursiveIntersectionCode
