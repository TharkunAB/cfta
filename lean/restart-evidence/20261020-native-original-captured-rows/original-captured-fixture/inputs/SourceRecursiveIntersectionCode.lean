import MicroCFTA.SourceRecursiveIntersectionThunkReadback

/-!
# Explicit source effects and recursive requests

The code retains ordered source effects and recursive request continuations.
Its interpretation exposes separate node and edge callbacks. Native memo
completion instructions affect only the memo state, so this source-machine
interpretation erases them.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Source code keeps its continuation at every physical effect and recursive request. -/
inductive Code (Symbol Guard : Type) : Type → Type 1 where
  | pure (value : A) : Code Symbol Guard A
  | fail (failure : Failure) : Code Symbol Guard A
  | work {X : Type} (job : Work Symbol Guard X) (next : X → Code Symbol Guard A) : Code Symbol Guard A
  | enter (domain : Interned DomainKey) (left right : Value Symbol Guard) (first second : Nat)
      (next : Interned DomainKey → Code Symbol Guard A) : Code Symbol Guard A
  | read (name : Nat) (next : Option (Value Symbol Guard) → Code Symbol Guard A) : Code Symbol Guard A
  | optionalBinder (key : Nat × Nat) (body : Value Symbol Guard)
      (next : Value Symbol Guard → Code Symbol Guard A) : Code Symbol Guard A
  | node (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A) : Code Symbol Guard A
  | edge (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A) : Code Symbol Guard A
  | finishNode (handle : Nat) (value : Value Symbol Guard) (next : Code Symbol Guard A) : Code Symbol Guard A
  | finishEdge (handle : Nat) (value : EdgeValue Symbol Guard) (next : Code Symbol Guard A) : Code Symbol Guard A

/-- Append a continuation without evaluating any source request. -/
def Code.bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) : Code Symbol Guard B :=
  match code with
  | .pure value => next value
  | .fail failure => .fail failure
  | .work job resume => .work job (fun value => (resume value).bind next)
  | .enter domain left right first second resume => .enter domain left right first second (fun value => (resume value).bind next)
  | .read name resume => .read name (fun value => (resume value).bind next)
  | .optionalBinder key body resume => .optionalBinder key body (fun value => (resume value).bind next)
  | .node request resume => .node request (fun value => (resume value).bind next)
  | .edge request resume => .edge request (fun value => (resume value).bind next)
  | .finishNode handle value rest => .finishNode handle value (rest.bind next)
  | .finishEdge handle value rest => .finishEdge handle value (rest.bind next)

/-- Appending continuations preserves their original order through every source instruction. -/
theorem Code.bind_assoc (code : Code Symbol Guard A) (first : A → Code Symbol Guard B) (second : B → Code Symbol Guard C) :
    (code.bind first).bind second = code.bind (fun value => (first value).bind second) := by
  induction code with
  | pure value | fail failure => rfl
  | work job resume ih | enter domain left right first second resume ih | read name resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih =>
    simp only [Code.bind, ih]
  | finishNode handle value rest ih | finishEdge handle value rest ih => simp only [Code.bind, ih]

/-- Keep each list request before the next request and the final continuation. -/
def walk (call : A → Code Symbol Guard B) : List A → Code Symbol Guard (List B)
  | [] => .pure []
  | first :: rest => (call first).bind fun value => (walk call rest).bind fun values => .pure (value :: values)

/-- One physical node callback receives its complete captured request. -/
abbrev NodeCall (Symbol Guard : Type) := NodeRequest Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)

/-- One physical edge callback receives its complete captured row request. -/
abbrev EdgeCall (Symbol Guard : Type) := EdgeRequest Symbol Guard → Machine Symbol Guard → Result Symbol Guard (EdgeValue Symbol Guard)

/-- Interpret actual source effects, using separate recursive node and edge callbacks. -/
def interpret [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Result Symbol Guard A :=
  match code with
  | .pure value => .done value state
  | .fail failure => .failed failure state
  | .work job next => (SourceRecursiveIntersectionKernel.work job state).bind fun value after => interpret nodes edges (next value) after
  | .enter domain left right first second next =>
      let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      interpret nodes edges (next entered.1) { state with domains := entered.2 }
  | .read name next => interpret nodes edges (next (SourcePreparedSharedRows.read state.heap name)) state
  | .optionalBinder key body next =>
      (construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state).bind fun value after =>
        interpret nodes edges (next value) after
  | .node request next => (nodes request state).bind fun value after => interpret nodes edges (next value) after
  | .edge request next => (edges request state).bind fun value after => interpret nodes edges (next value) after
  | .finishNode _ _ next | .finishEdge _ _ next => interpret nodes edges next state

/-- Source result sequencing is associative, including exact failed caches. -/
theorem result_bind_assoc (result : Result Symbol Guard A)
    (first : A → Machine Symbol Guard → Result Symbol Guard B)
    (second : B → Machine Symbol Guard → Result Symbol Guard C) :
    (result.bind first).bind second = result.bind (fun value after => (first value after).bind second) := by
  cases result <;> rfl

/-- Equal continuations give equal source results at their actual returned caches. -/
theorem result_bind_congr (result : Result Symbol Guard A)
    (first second : A → Machine Symbol Guard → Result Symbol Guard B)
    (same : ∀ value after, first value after = second value after) : result.bind first = result.bind second := by
  cases result with
  | done value after => exact same value after
  | failed => rfl

/-- Explicit code sequencing has the same exact source cache effects as result sequencing. -/
theorem interpret_bind [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : Machine Symbol Guard) :
    interpret nodes edges (code.bind next) state =
      (interpret nodes edges code state).bind (fun value after => interpret nodes edges (next value) after) := by
  induction code generalizing state with
  | pure value | fail failure => rfl
  | work job resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih =>
    simp only [Code.bind, interpret, result_bind_assoc]
    apply result_bind_congr
    intro value after
    exact ih value after
  | enter domain left right first second resume ih =>
    exact ih _ _
  | read name resume ih => exact ih _ _
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih state

/-- Ordered code walks interpret to the original stateful list worker. -/
theorem interpret_walk [DecidableEq (EdgeKey Symbol Guard)] (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (call : A → Code Symbol Guard B) (values : List A) (state : Machine Symbol Guard) :
    interpret nodes edges (walk call values) state =
      SourceRecursiveIntersectionKernel.walk (fun value => interpret nodes edges (call value)) values state := by
  induction values generalizing state with
  | nil => rfl
  | cons first rest ih =>
    simp only [walk, interpret_bind, SourceRecursiveIntersectionKernel.walk]
    apply result_bind_congr
    intro value after
    rw [ih]
    rfl

end MicroCFTA.SourceRecursiveIntersectionCode
