import MicroCFTA.EndpointGateClassModes

/-!
# Closed constrained Mu endpoints in the current gate

The source change at 418fe8d3 permits a closed constrained Mu at the end
of a secondary path. Interior and open constrained Mu values still refuse
the path. The primary worker retains its complete previous computation.
Predicates are pure inputs here. Their completed memo calls are separate.
-/
namespace MicroCFTA.SourceCurrentMuEndpoint
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open InternedFreshOrdinaryStatefulGate (anyKnown child)

/-- Retain source guard order and the new closed constrained-Mu endpoint branch. -/
def dispatch [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) : Outcome Symbol Guard (Option Bool) :=
  match value with
  | .reference _ | .union .. => .done (some true) state
  | _ =>
      if value.depth == 0 && value.free.isEmpty then .done (some false) state
      else match value with
        | .mu .. =>
            if !unconstrained value then
              match path with
              | [] => if value.free.isEmpty then .done (some belowEnd) state else .done (some true) state
              | _ :: _ => .done (some true) state
            else if value.free.isEmpty then .done (some false) state
            else (InternedFreshOrdinaryStoredSubstitution.unfold value state).bind fun next after =>
              recur path next after
        | _ => match path with
            | [] => .done (some (!value.free.isEmpty || (belowEnd && reaches value))) state
            | index :: rest => match value with
                | .node _ edges _ _ => anyKnown (fun edge current => child recur edge.children index rest current) edges state
                | _ => .done (some false) state

/-- Bound recursive gate calls and retain actual unfolding outcomes and heaps. -/
def nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool) :
    Nat → Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool)
  | 0, _, _, state => .done none state
  | fuel + 1, path, value, state => dispatch belowEnd unconstrained reaches (nodeMeets belowEnd unconstrained reaches fuel) path value state

/-- A forest path selects the original child before its node test. -/
def meets [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  match path with
  | [] => .done (some false) state
  | index :: rest => child (nodeMeets belowEnd unconstrained reaches fuel) values index rest state

/-- Ordered class scanning stops at the first true path and retains each returned heap. -/
def classMeets [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  anyKnown (fun path current => meets belowEnd unconstrained reaches fuel values path current) paths state

/-- The enabled primary dispatch is unchanged, including actual unfolding and short circuits. -/
theorem primary_dispatch [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) :
    dispatch true unconstrained reaches recur path value state =
      EndpointStatefulGate.dispatch unconstrained reaches recur path value state := by
  cases value <;> cases path <;> simp [dispatch, EndpointStatefulGate.dispatch]

/-- Every primary fuel amount has exactly its previous outcome and complete returned heap. -/
theorem primary_node [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    nodeMeets true unconstrained reaches fuel path value state =
      EndpointStatefulGate.nodeMeets unconstrained reaches fuel path value state := by
  induction fuel generalizing path value state with
  | zero => rfl
  | succ fuel ih =>
      simp only [nodeMeets, primary_dispatch, EndpointStatefulGate.nodeMeets]
      have same : nodeMeets true unconstrained reaches fuel = EndpointStatefulGate.nodeMeets unconstrained reaches fuel :=
        funext fun path => funext fun value => funext fun state => ih path value state
      rw [same]

/-- The primary forest-path worker preserves the exact former computation. -/
theorem primary_meets [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) :
    meets true unconstrained reaches fuel values path state =
      EndpointStatefulGate.meets unconstrained reaches fuel values path state := by
  cases path with
  | nil => rfl
  | cons index rest =>
      simp only [meets, EndpointStatefulGate.meets, child]
      split <;> simp only [primary_node]

/-- The primary class scan preserves every outcome, source short circuit, and heap. -/
theorem primary_class [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
    classMeets true unconstrained reaches fuel values paths state =
      EndpointStatefulGate.classMeets unconstrained reaches fuel values paths state := by
  simp only [classMeets, EndpointStatefulGate.classMeets, primary_meets]

/-- A nonempty-path dispatch retains the previous secondary operation for the same recursive callback. -/
theorem secondary_dispatch_nonroot [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (index : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) :
    dispatch false unconstrained reaches recur (index :: path) value state =
      InternedFreshOrdinaryStatefulGate.dispatch unconstrained recur (index :: path) value state := by
  cases value <;> simp [dispatch, InternedFreshOrdinaryStatefulGate.dispatch]

/-- A closed Mu endpoint performs its predicate test and returns the selected mode only when constrained. -/
theorem closed_mu [DecidableEq (EdgeKey Symbol Guard)]
    (belowEnd : Bool) (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (closed : (Value.mu entry body depth ordinary).free = []) :
    nodeMeets belowEnd unconstrained reaches (fuel + 1) [] (.mu entry body depth ordinary) state =
      .done (some (if unconstrained (.mu entry body depth ordinary) then false else belowEnd)) state := by
  cases plain : unconstrained (.mu entry body depth ordinary) <;>
    simp [nodeMeets, dispatch, Value.depth, plain, closed]

/-- A closed constrained Mu at the exact endpoint returns the source mode without unfolding. -/
theorem closed_constrained [DecidableEq (EdgeKey Symbol Guard)]
    (belowEnd : Bool) (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (blocked : unconstrained (.mu entry body depth ordinary) = false)
    (closed : (Value.mu entry body depth ordinary).free = []) :
    nodeMeets belowEnd unconstrained reaches (fuel + 1) [] (.mu entry body depth ordinary) state = .done (some belowEnd) state := by
  simp [nodeMeets, dispatch, Value.depth, blocked, closed]

/-- A constrained Mu inside a path still refuses without unfolding. -/
theorem constrained_interior [DecidableEq (EdgeKey Symbol Guard)]
    (belowEnd : Bool) (unconstrained reaches : Value Symbol Guard → Bool) (fuel index : Nat) (path : Path)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (blocked : unconstrained (.mu entry body depth ordinary) = false) :
    nodeMeets belowEnd unconstrained reaches (fuel + 1) (index :: path) (.mu entry body depth ordinary) state = .done (some true) state := by
  simp [nodeMeets, dispatch, Value.depth, blocked]

/-- An open constrained Mu at the endpoint still refuses without unfolding. -/
theorem constrained_open [DecidableEq (EdgeKey Symbol Guard)]
    (belowEnd : Bool) (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (blocked : unconstrained (.mu entry body depth ordinary) = false)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    nodeMeets belowEnd unconstrained reaches (fuel + 1) [] (.mu entry body depth ordinary) state = .done (some true) state := by
  simp [nodeMeets, dispatch, Value.depth, blocked, List.isEmpty_eq_false_iff.mpr opened]

/-- The former secondary worker refuses the newly permitted closed endpoint. -/
theorem previous_secondary [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (fuel : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (blocked : unconstrained (.mu entry body depth ordinary) = false) :
    InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained (fuel + 1) [] (.mu entry body depth ordinary) state = .done (some true) state := by
  simp [InternedFreshOrdinaryStatefulGate.nodeMeets, InternedFreshOrdinaryStatefulGate.dispatch, Value.depth, blocked]

/-- Closed endpoint records admitted by the secondary tag tests. -/
inductive ClosedEndpoint : Value Symbol Guard → Prop where
  | empty : ClosedEndpoint .empty
  | node (closed : (Value.node entry edges depth free).free = []) : ClosedEndpoint (.node entry edges depth free)
  | mu (closed : (Value.mu entry body depth ordinary).free = []) : ClosedEndpoint (.mu entry body depth ordinary)

/-- Every admitted endpoint is closed; unrelated original children need not be closed. -/
theorem ClosedEndpoint.closed {value : Value Symbol Guard} (endpoint : ClosedEndpoint value) : value.free = [] := by
  cases endpoint with
  | empty => rfl
  | node closed | mu closed => exact closed

/-- The secondary endpoint test accepts closed ordinary and recursive records in one step. -/
theorem closed_endpoint [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (endpoint : ClosedEndpoint value) :
    nodeMeets false unconstrained reaches (fuel + 1) [] value state = .done (some false) state := by
  cases endpoint with
  | empty => simp [nodeMeets, dispatch, Value.depth, Value.free]
  | node closed => simp [nodeMeets, dispatch, closed]
  | mu closed => simp [nodeMeets, dispatch, Value.depth, closed]

/-- A class can end at selected closed records while other original children remain open. -/
def ClosedEndpoints (values : List (Value Symbol Guard)) (paths : Class) : Prop :=
  ∀ path ∈ paths, ∃ index value, path = [index] ∧ values[index]? = some value ∧ ClosedEndpoint value

/-- Every such ordered class completes the new secondary scan with no constructor change. -/
theorem closed_endpoints_class [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (endpoints : ClosedEndpoints values paths) :
    classMeets false unconstrained reaches (fuel + 1) values paths state = .done (some false) state := by
  induction paths with
  | nil => rfl
  | cons path rest ih =>
      obtain ⟨index, value, rfl, selected, endpoint⟩ := endpoints path List.mem_cons_self
      have head := closed_endpoint unconstrained reaches fuel value state endpoint
      have tail := ih (fun path member => endpoints path (List.mem_cons_of_mem _ member))
      simpa only [classMeets, anyKnown, meets, child, selected, head, Outcome.bind] using tail

/-- A class starting at a closed constrained Mu is refused by the primary mode and admitted by the new secondary mode. -/
theorem candidate_class [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel index : Nat)
    (values : List (Value Symbol Guard)) (rest : Class)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (selected : values[index]? = some (.mu entry body depth ordinary))
    (blocked : unconstrained (.mu entry body depth ordinary) = false)
    (closed : (Value.mu entry body depth ordinary).free = []) (endpoints : ClosedEndpoints values rest) :
    classMeets true unconstrained reaches (fuel + 1) values ([index] :: rest) state = .done (some true) state ∧
    classMeets false unconstrained reaches (fuel + 1) values ([index] :: rest) state = .done (some false) state := by
  constructor
  · have first := closed_constrained true unconstrained reaches fuel entry body depth ordinary state blocked closed
    simp only [classMeets, anyKnown, meets, child, selected, first, Outcome.bind]
  · apply closed_endpoints_class unconstrained reaches fuel values ([index] :: rest) state
    intro path member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨index, .mu entry body depth ordinary, rfl, selected, .mu closed⟩
    · exact endpoints path later

end MicroCFTA.SourceCurrentMuEndpoint
