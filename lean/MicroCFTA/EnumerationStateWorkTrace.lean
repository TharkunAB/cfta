import MicroCFTA.EnumerationState

/-!
# State and work observations for selected-slot expansion

The tree follows the existing node, edge, and selected-slot stages.
It retains states before rejection and errors. It sums all alternatives.
Work counts state, branch, and sequencing transitions in this model.
Graph operations and union-find functions are atomic at this level.
This file does not derive sufficient fuel or a native runtime bound.
-/
set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateWorkTrace
open EnumerationState Fragments

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem list_lawful : LawfulMonad List := by
  exact LawfulMonad.mk' (m := List)
    (id_map := by intros; simp [Functor.map])
    (bind_pure_comp := by
      intro α β f values
      induction values with
      | nil => rfl
      | cons first rest ih => simp_all [Bind.bind, Functor.map, Pure.pure, List.flatMap])
    (pure_bind := by intros; simp [Bind.bind, Pure.pure])
    (bind_assoc := by intros; simp [Bind.bind, List.flatMap_assoc])

attribute [local instance] list_lawful

/-- A finite execution retains state at every outcome and operation. -/
inductive Tree (Symbol Guard α : Type) where
  | done (value : α) (state : State Symbol Guard)
  | failed (error : Error) (state : State Symbol Guard)
  | rejected (state : State Symbol Guard)
  | step (state : State Symbol Guard) (next : Tree Symbol Guard α)
  | fork (state : State Symbol Guard) (left right : Tree Symbol Guard α)

namespace Tree
variable {Symbol Guard α β : Type}

/-- Continue every successful branch in its own returned state. -/
def bind (tree : Tree Symbol Guard α)
    (next : α → State Symbol Guard → Tree Symbol Guard β) : Tree Symbol Guard β :=
  match tree with
  | .done value state => .step state (next value state)
  | .failed error state => .failed error state
  | .rejected state => .rejected state
  | .step state rest => .step state (bind rest next)
  | .fork state left right => .fork state (bind left next) (bind right next)

/-- Remove observations and retain the current stage's ordered result list. -/
def erase : Tree Symbol Guard α → List (Except Error (α × State Symbol Guard))
  | .done value state => [.ok (value, state)]
  | .failed error _ => [.error error]
  | .rejected _ => []
  | .step _ next => erase next
  | .fork _ left right => erase left ++ erase right

/-- Retain states on successful, failed, and rejected branches. -/
def states : Tree Symbol Guard α → List (State Symbol Guard)
  | .done _ state | .failed _ state | .rejected state => [state]
  | .step state next => state :: states next
  | .fork state left right => state :: (states left ++ states right)

/-- Retain the error and its reached state before erasure. -/
def failures : Tree Symbol Guard α → List (Error × State Symbol Guard)
  | .done _ _ | .rejected _ => []
  | .failed error state => [(error, state)]
  | .step _ next => failures next
  | .fork _ left right => failures left ++ failures right

/-- Successful leaves determine the actual calls to the continuation. -/
def successes : Tree Symbol Guard α → List (α × State Symbol Guard)
  | .done value state => [(value, state)]
  | .failed _ _ | .rejected _ => []
  | .step _ next => successes next
  | .fork _ left right => successes left ++ successes right

/-- Count every executed alternative, including errors and rejection. -/
def work : Tree Symbol Guard α → Nat
  | .done _ _ => 0
  | .failed _ _ | .rejected _ => 1
  | .step _ next => 1 + work next
  | .fork _ left right => 1 + work left + work right

/-- Tree composition erases to the current state, error, and list bind. -/
theorem erase_bind (tree : Tree Symbol Guard α)
    (next : α → State Symbol Guard → Tree Symbol Guard β) :
    erase (bind tree next) = (erase tree).flatMap (fun result =>
      match result with
      | .error error => [.error error]
      | .ok (value, state) => erase (next value state)) := by
  induction tree with
  | done value state => simp only [bind, erase, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | failed error state => rfl
  | rejected state => rfl
  | step state rest ih => exact ih
  | fork state left right ihLeft ihRight =>
      simp only [bind, erase, List.flatMap_append, ihLeft, ihRight]

/-- Total continuation work is a sum over all successful leaves. -/
theorem work_bind (tree : Tree Symbol Guard α)
    (next : α → State Symbol Guard → Tree Symbol Guard β) :
    work (bind tree next) = work tree +
      ((successes tree).map fun result => 1 + work (next result.1 result.2)).sum := by
  induction tree with
  | done value state => simp [bind, work, successes]
  | failed error state => rfl
  | rejected state => rfl
  | step state rest ih =>
      simp only [bind, work, successes, ih]
      omega
  | fork state left right ihLeft ihRight =>
      simp only [bind, work, successes, List.map_append, List.sum_append, ihLeft, ihRight]
      omega

/-- Composition retains every earlier state, including intermediate successes. -/
theorem states_bind_left (tree : Tree Symbol Guard α)
    (next : α → State Symbol Guard → Tree Symbol Guard β)
    (state : State Symbol Guard) (member : state ∈ states tree) :
    state ∈ states (bind tree next) := by
  induction tree with
  | done value before =>
      have same := List.mem_singleton.mp member
      subst state
      exact List.mem_cons_self
  | failed error before => exact member
  | rejected before => exact member
  | step before rest ih =>
      rcases List.mem_cons.mp member with same | later
      · exact List.mem_cons.mpr (.inl same)
      · exact List.mem_cons.mpr (.inr (ih later))
  | fork before left right ihLeft ihRight =>
      rcases List.mem_cons.mp member with same | later
      · exact List.mem_cons.mpr (.inl same)
      · rcases List.mem_append.mp later with inLeft | inRight
        · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inl (ihLeft inLeft))))
        · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inr (ihRight inRight))))

/-- Every erased error retains a reached state in the execution tree. -/
theorem error_iff (tree : Tree Symbol Guard α) (error : Error) :
    .error error ∈ erase tree ↔ ∃ state, (error, state) ∈ failures tree := by
  induction tree with
  | done value state => simp [erase, failures]
  | failed other state => simp [erase, failures, Prod.mk.injEq]
  | rejected state => simp [erase, failures]
  | step state rest ih => exact ih
  | fork state left right ihLeft ihRight =>
      simp only [erase, failures, List.mem_append, ihLeft, ihRight]
      constructor
      · rintro (⟨reached, member⟩ | ⟨reached, member⟩)
        · exact ⟨reached, .inl member⟩
        · exact ⟨reached, .inr member⟩
      · rintro ⟨reached, member | member⟩
        · exact .inl ⟨reached, member⟩
        · exact .inr ⟨reached, member⟩

/-- Reached error states also occur in the complete state observation list. -/
theorem failure_state_mem (tree : Tree Symbol Guard α) (error : Error)
    (state : State Symbol Guard) (member : (error, state) ∈ failures tree) :
    state ∈ states tree := by
  induction tree with
  | done value before => cases member
  | failed other before =>
      have same := List.mem_singleton.mp member
      cases same
      exact List.mem_singleton_self _
  | rejected before => cases member
  | step before rest ih => exact List.mem_cons.mpr (.inr (ih member))
  | fork before left right ihLeft ihRight =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inl (ihLeft inLeft))))
      · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inr (ihRight inRight))))
end Tree

/-- An execution starts at the stage's actual input state. -/
abbrev M (Symbol Guard α : Type) := State Symbol Guard → Tree Symbol Guard α

variable {Symbol Guard α β : Type}

def pure (value : α) : M Symbol Guard α := fun state => .done value state

def bind (action : M Symbol Guard α) (next : α → M Symbol Guard β) : M Symbol Guard β :=
  fun state => Tree.bind (action state) next

instance : Monad (M Symbol Guard) where
  pure := pure
  bind := bind

/-- Forget observations without changing the existing stage results. -/
def erase (action : M Symbol Guard α) : EnumerateM Symbol Guard α :=
  fun state => Tree.erase (action state)

theorem erase_pure (value : α) :
    erase (pure value : M Symbol Guard α) = (Pure.pure value : EnumerateM Symbol Guard α) := rfl

theorem erase_bind (action : M Symbol Guard α) (next : α → M Symbol Guard β) :
    erase (action >>= next) = (erase action >>= fun value => erase (next value)) := by
  funext state
  dsimp only [erase, Bind.bind, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, ExceptT.run, Pure.pure]
  rw [Tree.erase_bind]
  apply congrArg (fun continuation => List.flatMap continuation (Tree.erase (action state)))
  funext result
  cases result with
  | error error => rfl
  | ok pair => cases pair; rfl

def get : M Symbol Guard (State Symbol Guard) :=
  fun state => .step state (.done state state)

def modify (update : State Symbol Guard → State Symbol Guard) : M Symbol Guard Unit :=
  fun state => .step state (.done () (update state))

def set (state : State Symbol Guard) : M Symbol Guard Unit := modify (fun _ => state)

def reject : M Symbol Guard α := fun state => .rejected state

def failure (error : Error) : M Symbol Guard α := fun state => .failed error state

def require (condition : Bool) : M Symbol Guard Unit :=
  fun state => .step state ((if condition then pure () else reject) state)

theorem erase_get :
    erase (get : M Symbol Guard (State Symbol Guard)) =
      (MonadState.get : EnumerateM Symbol Guard (State Symbol Guard)) := rfl

theorem erase_modify (update : State Symbol Guard → State Symbol Guard) :
    erase (modify update) = (_root_.modify update : EnumerateM Symbol Guard Unit) := rfl

theorem erase_set (state : State Symbol Guard) :
    erase (set state) = (MonadStateOf.set state : EnumerateM Symbol Guard Unit) := rfl

theorem erase_reject :
    erase (reject : M Symbol Guard α) = (EnumerationState.reject : EnumerateM Symbol Guard α) := rfl

theorem erase_failure (error : Error) :
    erase (failure error : M Symbol Guard α) = (EnumerationState.failure error : EnumerateM Symbol Guard α) := rfl

theorem erase_require (condition : Bool) :
    erase (require condition : M Symbol Guard Unit) = EnumerationState.require condition := by
  cases condition <;> rfl

/-- The source list choice visits each alternative with the same input state. -/
def choose : List α → M Symbol Guard α
  | [] => reject
  | value :: rest => fun state => .fork state (.done value state) (choose rest state)

theorem erase_choose (values : List α) :
    erase (choose values : M Symbol Guard α) = EnumerationState.choose values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      funext state
      change .ok (first, state) :: Tree.erase (choose rest state) = _
      exact congrArg (List.cons (.ok (first, state))) (congrFun ih state)

/-- Process children in source order and retain each branch's intermediate state. -/
def mapEach (action : α → M Symbol Guard β) : List α → M Symbol Guard (List β)
  | [] => pure []
  | value :: rest => do
      let result ← action value
      let results ← mapEach action rest
      pure (result :: results)

private theorem source_mapM_cons (action : α → EnumerateM Symbol Guard β)
    (first : α) (rest : List α) :
    (first :: rest).mapM action =
      (do let value ← action first; let tail ← rest.mapM action; Pure.pure (value :: tail)) := by
  simp

theorem erase_mapEach (action : α → M Symbol Guard β) (values : List α) :
    erase (mapEach action values) = values.mapM (fun value => erase (action value)) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simp only [mapEach, erase_bind, erase_pure, source_mapM_cons, ih]

def forEach (action : α → M Symbol Guard Unit) : List α → M Symbol Guard Unit
  | [] => pure ()
  | value :: rest => do
      action value
      forEach action rest

theorem erase_forEach (action : α → M Symbol Guard Unit) (values : List α) :
    erase (forEach action values) = values.forM (fun value => erase (action value)) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      change erase (action first >>= fun _ => forEach action rest) =
        (erase (action first) >>= fun _ => rest.forM (fun value => erase (action value)))
      rw [erase_bind, ih]

def setValue (uv : Nat) (value : UVarValue Symbol) : M Symbol Guard Unit :=
  modify fun state => {state with values := state.values.set uv value}

def rawValue (uv : Nat) : M Symbol Guard (UVarValue Symbol) := do
  match (← get).values[uv]? with
  | none => failure .invalidSlot
  | some value => pure value

def representative (fuel uv : Nat) : M Symbol Guard Nat := do
  let state ← get
  match UnionFind.findRoot fuel state.representatives uv with
  | none => failure .representativeFuel
  | some found =>
      set {state with representatives := found.forest}
      pure found.representative

def getValue (fuel uv : Nat) : M Symbol Guard (UVarValue Symbol) := do
  rawValue (← representative fuel uv)

def inheritAncestry (uv : Nat) : M Symbol Guard Unit :=
  modify fun state => {state with recursionAncestry := (fun other =>
    if other = uv then (state.expansionAncestry ++ state.recursionAncestry uv).eraseDups
    else state.recursionAncestry other)}

def allocate (node : Option Nat) : M Symbol Guard Nat := do
  let state ← get
  let uv := state.counter
  set {state with counter := uv + 1, values := state.values ++ [UVarValue.unenumerated node []]}
  inheritAncestry uv
  pure uv

def suspend (trie : EqualityTrie.Trie) : M Symbol Guard Suspended := do
  pure ⟨trie, ← allocate none⟩

def assimilate (graph : Graph Symbol Guard) (target source : Nat) : M Symbol Guard Unit := do
  if target = source then pure () else
    let sourceValue ← rawValue source
    match sourceValue with
    | .eliminated => pure ()
    | _ =>
        let targetValue ← rawValue target
        match intersectValues graph sourceValue targetValue with
        | none => failure .invalidIntersection
        | some merged =>
            require (!hasEmptyContents graph merged)
            setValue target merged
            setValue source .eliminated
            modify fun state => {state with recursionAncestry := (fun other =>
              if other = target then
                (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
              else state.recursionAncestry other)}

def mergeNode (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    M Symbol Guard Unit := do
  let root ← representative fuel uv
  let previous ← rawValue root
  match intersectValues graph (.unenumerated (some node) scs) previous with
  | none => failure .invalidIntersection
  | some merged =>
      setValue root merged
      inheritAncestry root
      require (!hasEmptyContents graph merged)

def unionVariables (fuel left right : Nat) : M Symbol Guard Unit := do
  let state ← get
  match UnionFind.union fuel fuel state.representatives left right with
  | none => failure .representativeFuel
  | some forest => set {state with representatives := forest}

theorem erase_setValue (uv : Nat) (value : UVarValue Symbol) :
    erase (setValue uv value : M Symbol Guard Unit) = EnumerationState.setValue uv value := rfl

theorem erase_rawValue (uv : Nat) :
    erase (rawValue uv : M Symbol Guard (UVarValue Symbol)) = EnumerationState.rawValue uv := by
  unfold rawValue EnumerationState.rawValue
  rw [erase_bind, erase_get]
  congr 1
  funext state
  cases state.values[uv]? <;> simp only [erase_failure, erase_pure]

theorem erase_representative (fuel uv : Nat) :
    erase (representative fuel uv : M Symbol Guard Nat) = EnumerationState.representative fuel uv := by
  unfold representative EnumerationState.representative
  rw [erase_bind, erase_get]
  congr 1
  funext state
  cases UnionFind.findRoot fuel state.representatives uv <;>
    simp only [erase_failure, erase_bind, erase_set, erase_pure]

theorem erase_getValue (fuel uv : Nat) :
    erase (getValue fuel uv : M Symbol Guard (UVarValue Symbol)) = EnumerationState.getValue fuel uv := by
  simp only [getValue, EnumerationState.getValue, erase_bind, erase_representative, erase_rawValue]

theorem erase_inheritAncestry (uv : Nat) :
    erase (inheritAncestry uv : M Symbol Guard Unit) = EnumerationState.inheritAncestry uv := by
  unfold inheritAncestry EnumerationState.inheritAncestry
  exact erase_modify _

theorem erase_allocate (node : Option Nat) :
    erase (allocate node : M Symbol Guard Nat) = EnumerationState.allocate node := by
  simp only [allocate, EnumerationState.allocate, erase_bind, erase_get, erase_set,
    erase_inheritAncestry, erase_pure]

theorem erase_suspend (trie : EqualityTrie.Trie) :
    erase (suspend trie : M Symbol Guard Suspended) = EnumerationState.suspend trie := by
  simp only [suspend, EnumerationState.suspend, erase_bind, erase_allocate, erase_pure]

theorem erase_assimilate (graph : Graph Symbol Guard) (target source : Nat) :
    erase (assimilate graph target source) = EnumerationState.assimilate graph target source := by
  unfold assimilate EnumerationState.assimilate
  split
  · exact erase_pure ()
  · rw [erase_bind, erase_rawValue]
    congr 1
    funext sourceValue
    cases sourceValue with
    | eliminated => exact erase_pure ()
    | unenumerated node scs =>
        rw [erase_bind, erase_rawValue]
        congr 1
        funext targetValue
        cases intersectValues graph (.unenumerated node scs) targetValue <;>
          simp only [erase_failure, erase_bind, erase_require, erase_setValue, erase_modify]
    | enumerated fragment =>
        rw [erase_bind, erase_rawValue]
        congr 1

theorem erase_mergeNode (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    erase (mergeNode graph fuel uv node scs) = EnumerationState.mergeNode graph fuel uv node scs := by
  unfold mergeNode EnumerationState.mergeNode
  rw [erase_bind, erase_representative]
  congr 1
  funext root
  rw [erase_bind, erase_rawValue]
  congr 1
  funext previous
  cases intersectValues graph (.unenumerated (some node) scs) previous <;>
    simp only [erase_failure, erase_bind, erase_setValue, erase_inheritAncestry, erase_require]

theorem erase_unionVariables (fuel left right : Nat) :
    erase (unionVariables fuel left right : M Symbol Guard Unit) = EnumerationState.unionVariables fuel left right := by
  unfold unionVariables EnumerationState.unionVariables
  rw [erase_bind, erase_get]
  congr 1
  funext state
  cases UnionFind.union fuel fuel state.representatives left right <;>
    simp only [erase_failure, erase_set]

mutual
  /-- Execute every actual node alternative and retain failed branch states. -/
  def enumerateNode (graph : Graph Symbol Guard) : Nat → List Suspended → Nat →
      M Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, node => do
        match graph.node node with
        | .empty => reject
        | view =>
          let here := scs.filter fun sc => EqualityTrie.isTerminal sc.trie
          let below := scs.filter fun sc => !EqualityTrie.isTerminal sc.trie
          match here with
          | [] =>
            match view with
            | .empty => reject
            | .recursive _ => pure (.hole (← allocate (some node)))
            | .alternatives edges => enumerateEdge graph fuel scs (← choose edges)
            | .unresolved _ => failure .unresolvedReference
          | first :: rest =>
            let roots ← mapEach (fun sc => representative (fuel + 1) sc.var) here
            forEach (fun sc => unionVariables (fuel + 1) first.var sc.var) rest
            let root ← representative (fuel + 1) first.var
            forEach (assimilate graph root) roots
            mergeNode graph (fuel + 1) root node below
            pure (.hole root)

  /-- Execute equality allocation and every child product in source order. -/
  def enumerateEdge (graph : Graph Symbol Guard) : Nat → List Suspended → Edge Symbol Guard →
      M Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, edge => do
        require (arityAllows edge.children.length scs)
        let added ← mapEach suspend edge.equalities
        let children ← mapEach (fun (node, index) =>
          enumerateNode graph fuel (descendScs index (scs ++ added)) node) edge.children.zipIdx
        let fragment := Fragment.node edge.symbol children
        match edge.residual with
        | none => pure ()
        | some guard => modify fun state => {state with obligations := (guard, fragment) :: state.obligations}
        pure fragment
end

private theorem erase_node_edge (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node, erase (enumerateNode graph fuel scs node) = EnumerationState.enumerateNode graph fuel scs node) ∧
    (∀ scs edge, erase (enumerateEdge graph fuel scs edge) = EnumerationState.enumerateEdge graph fuel scs edge) := by
  induction fuel with
  | zero => constructor <;> intros <;> rfl
  | succ fuel ih =>
      constructor
      · intro scs node
        cases view : graph.node node with
        | empty => simp only [enumerateNode, EnumerationState.enumerateNode, view, erase_reject]
        | recursive body | alternatives edges | unresolved missing =>
            cases here : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil =>
                simp only [enumerateNode, EnumerationState.enumerateNode, view, here,
                  erase_bind, erase_pure, erase_allocate, erase_choose, ih.2, erase_failure]
            | cons first rest =>
                simp only [enumerateNode, EnumerationState.enumerateNode, view, here,
                  erase_bind, erase_mapEach, erase_forEach, erase_representative,
                  erase_unionVariables, erase_assimilate, erase_mergeNode, erase_pure]
      · intro scs edge
        simp only [enumerateEdge, EnumerationState.enumerateEdge, erase_bind,
          erase_require, erase_mapEach, erase_suspend, ih.1]
        congr 1
        funext ignored
        congr 1
        funext added
        congr 1
        funext children
        cases edge.residual <;> simp only [erase_bind, erase_pure, erase_modify, pure_bind]

/-- Node observations erase to the current worker for every fuel and input state. -/
theorem erase_enumerateNode (graph : Graph Symbol Guard) (fuel : Nat) (scs : List Suspended) (node : Nat) :
    erase (enumerateNode graph fuel scs node) = EnumerationState.enumerateNode graph fuel scs node :=
  (erase_node_edge graph fuel).1 scs node

/-- Edge observations erase to the current worker, including failed products. -/
theorem erase_enumerateEdge (graph : Graph Symbol Guard) (fuel : Nat) (scs : List Suspended) (edge : Edge Symbol Guard) :
    erase (enumerateEdge graph fuel scs edge) = EnumerationState.enumerateEdge graph fuel scs edge :=
  (erase_node_edge graph fuel).2 scs edge

/-- Execute the actual selected-slot expansion and its final slot write. -/
def enumerateOut (graph : Graph Symbol Guard) (fuel uv : Nat) : M Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) uv with
  | .unenumerated (some node) scs =>
      let root ← representative (fuel + 1) uv
      let ancestry := (← get).recursionAncestry root
      modify fun state => {state with expansionAncestry := (
        match graph.node node with
        | .recursive _ => (recursionKey node scs :: ancestry).eraseDups
        | _ => ancestry)}
      let fragment ← enumerateNode graph fuel scs
        (match graph.node node with | .recursive body => body | _ => node)
      modify fun state => {state with expansionAncestry := []}
      setValue root (.enumerated fragment)
      pure fragment
  | _ => reject

/-- Selected-slot observations erase to the current stage without a success premise. -/
theorem erase_enumerateOut (graph : Graph Symbol Guard) (fuel uv : Nat) :
    erase (enumerateOut graph fuel uv) = EnumerationState.enumerateOut graph fuel uv := by
  unfold enumerateOut EnumerationState.enumerateOut
  rw [erase_bind, erase_getValue]
  congr 1
  funext value
  cases value with
  | eliminated | enumerated fragment => exact erase_reject
  | unenumerated node scs =>
      cases node with
      | none => exact erase_reject
      | some node =>
          simp only [erase_bind, erase_representative, erase_get, erase_modify,
            erase_enumerateNode, erase_setValue, erase_pure]
          rfl

/-- An actual selected-slot error has a retained reached state. -/
theorem enumerateOut_error_state (graph : Graph Symbol Guard) (fuel uv : Nat)
    (before : State Symbol Guard) (error : Error)
    (observed : .error error ∈ ExceptT.run (EnumerationState.enumerateOut graph fuel uv before)) :
    ∃ reached, (error, reached) ∈ (enumerateOut graph fuel uv before).failures ∧
      reached ∈ (enumerateOut graph fuel uv before).states := by
  have erased : .error error ∈ (enumerateOut graph fuel uv before).erase := by
    simpa only [← erase_enumerateOut, erase, ExceptT.run] using observed
  obtain ⟨reached, retained⟩ := (Tree.error_iff _ error).mp erased
  exact ⟨reached, retained, Tree.failure_state_mem _ error reached retained⟩

end MicroCFTA.EnumerationStateWorkTrace
