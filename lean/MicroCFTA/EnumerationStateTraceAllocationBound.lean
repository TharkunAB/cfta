import MicroCFTA.EnumerationStateDriverWorkTrace

/-!
# Counter bounds for every recorded enumeration state

The bound includes states on rejected and failed branches.
It uses the actual sum of work in the checked execution tree.
The concrete worker theorems have no caller resource premise.
This file does not bound work from the original input or count native costs.
-/
set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateTraceAllocationBound
open EnumerationStateWorkTrace
open EnumerationState (State Graph Edge Suspended UVarValue)

variable {Symbol Guard α β : Type}

/-- A stage bounds every recorded counter by its input counter and actual work. -/
def CounterAt (action : M Symbol Guard α) (before : State Symbol Guard) : Prop :=
  ∀ reached, reached ∈ (action before).states →
    reached.counter ≤ before.counter + (action before).work

/-- The counter bound applies at every input, including invalid input states. -/
def CounterBound (action : M Symbol Guard α) : Prop := ∀ before, CounterAt action before

/-- A successful leaf's state occurs in the complete state list. -/
theorem success_state_mem (tree : Tree Symbol Guard α) (value : α)
    (state : State Symbol Guard) (member : (value, state) ∈ tree.successes) :
    state ∈ tree.states := by
  induction tree with
  | done first before =>
      have same := List.mem_singleton.mp member
      cases same
      exact List.mem_singleton_self _
  | failed error before => cases member
  | rejected before => cases member
  | step before rest ih => exact List.mem_cons.mpr (.inr (ih member))
  | fork before left right ihLeft ihRight =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inl (ihLeft inLeft))))
      · exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inr (ihRight inRight))))

/-- A composed state comes from the first stage or an actual successful continuation. -/
theorem states_bind_cases (tree : Tree Symbol Guard α)
    (next : α → State Symbol Guard → Tree Symbol Guard β) (state : State Symbol Guard)
    (member : state ∈ (tree.bind next).states) :
    state ∈ tree.states ∨ ∃ value middle,
      (value, middle) ∈ tree.successes ∧ state ∈ (next value middle).states := by
  induction tree with
  | done value before =>
      rcases List.mem_cons.mp member with same | later
      · exact .inl (List.mem_singleton.mpr same)
      · exact .inr ⟨value, before, List.mem_singleton_self _, later⟩
  | failed error before => exact .inl member
  | rejected before => exact .inl member
  | step before rest ih =>
      rcases List.mem_cons.mp member with same | later
      · exact .inl (List.mem_cons.mpr (.inl same))
      · rcases ih later with earlier | ⟨value, middle, present, reached⟩
        · exact .inl (List.mem_cons.mpr (.inr earlier))
        · exact .inr ⟨value, middle, present, reached⟩
  | fork before left right ihLeft ihRight =>
      rcases List.mem_cons.mp member with same | later
      · exact .inl (List.mem_cons.mpr (.inl same))
      · rcases List.mem_append.mp later with inLeft | inRight
        · rcases ihLeft inLeft with earlier | ⟨value, middle, present, reached⟩
          · exact .inl (List.mem_cons.mpr (.inr (List.mem_append.mpr (.inl earlier))))
          · exact .inr ⟨value, middle, List.mem_append.mpr (.inl present), reached⟩
        · rcases ihRight inRight with earlier | ⟨value, middle, present, reached⟩
          · exact .inl (List.mem_cons.mpr (.inr (List.mem_append.mpr (.inr earlier))))
          · exact .inr ⟨value, middle, List.mem_append.mpr (.inr present), reached⟩

private theorem cost_le_sum (cost : α → Nat) (values : List α) (value : α)
    (member : value ∈ values) : cost value ≤ (values.map cost).sum := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst value
        simp only [List.map_cons, List.sum_cons]
        omega
      · have bound := ih later
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Sequencing uses the sum of all actual continuation work. -/
theorem counterAt_bind (action : M Symbol Guard α) (next : α → M Symbol Guard β)
    (before : State Symbol Guard) (first : CounterAt action before)
    (rest : ∀ value middle, (value, middle) ∈ (action before).successes → CounterAt (next value) middle) :
    CounterAt (action >>= next) before := by
  intro reached member
  change reached ∈ ((action before).bind next).states at member
  change reached.counter ≤ before.counter + ((action before).bind next).work
  rw [Tree.work_bind]
  rcases states_bind_cases (action before) next reached member with earlier |
      ⟨value, middle, present, later⟩
  · have bound := first reached earlier
    omega
  · have inputBound := first middle (success_state_mem _ value middle present)
    have outputBound := rest value middle present reached later
    have charged := cost_le_sum
      (fun result : α × State Symbol Guard => 1 + (next result.1 result.2).work)
      (action before).successes (value, middle) present
    dsimp only at charged
    omega

/-- Uniform component bounds compose without a lawfulness assumption on traces. -/
theorem counter_bind (action : M Symbol Guard α) (next : α → M Symbol Guard β)
    (first : CounterBound action) (rest : ∀ value, CounterBound (next value)) :
    CounterBound (action >>= next) := by
  intro before
  exact counterAt_bind action next before (first before) (fun value middle _ => rest value middle)

theorem pure_counterBound (value : α) : CounterBound (EnumerationStateWorkTrace.pure value : M Symbol Guard α) := by
  intro before reached member
  have same := List.mem_singleton.mp member
  subst reached
  exact Nat.le_refl _

theorem get_counterBound : CounterBound (get : M Symbol Guard (State Symbol Guard)) := by
  intro before reached member
  change reached ∈ [before, before] at member
  have same : reached = before := by simpa using member
  subst reached
  change before.counter ≤ before.counter + 1
  omega

/-- One traced write can pay for one newly allocated slot. -/
theorem modify_counterAt (update : State Symbol Guard → State Symbol Guard) (before : State Symbol Guard)
    (increment : (update before).counter ≤ before.counter + 1) : CounterAt (modify update) before := by
  intro reached member
  change reached ∈ [before, update before] at member
  change reached.counter ≤ before.counter + 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · omega
  · exact increment

theorem modify_counterBound (update : State Symbol Guard → State Symbol Guard)
    (increment : ∀ before, (update before).counter ≤ before.counter + 1) : CounterBound (modify update) :=
  fun before => modify_counterAt update before (increment before)

theorem set_counterAt (after before : State Symbol Guard)
    (increment : after.counter ≤ before.counter + 1) : CounterAt (set after) before :=
  modify_counterAt (fun _ => after) before increment

theorem reject_counterBound : CounterBound (reject : M Symbol Guard α) := by
  intro before reached member
  have same := List.mem_singleton.mp member
  subst reached
  change before.counter ≤ before.counter + 1
  omega

theorem failure_counterBound (error : EnumerationState.Error) : CounterBound (failure error : M Symbol Guard α) := by
  intro before reached member
  have same := List.mem_singleton.mp member
  subst reached
  change before.counter ≤ before.counter + 1
  omega

theorem require_counterBound (condition : Bool) : CounterBound (require condition : M Symbol Guard Unit) := by
  intro before reached member
  cases condition <;>
    simp only [require, reject, EnumerationStateWorkTrace.pure, Tree.states, Tree.work,
      Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member ⊢ <;>
    rcases member with rfl | rfl <;> omega

theorem choose_counterBound (values : List α) : CounterBound (choose values : M Symbol Guard α) := by
  induction values with
  | nil => exact reject_counterBound
  | cons first rest ih =>
      intro before reached member
      change reached ∈ before :: ([before] ++ (choose rest before).states) at member
      change reached.counter ≤ before.counter + (1 + 0 + (choose rest before).work)
      rcases List.mem_cons.mp member with same | later
      · subst reached; omega
      · rcases List.mem_append.mp later with firstState | restState
        · have same := List.mem_singleton.mp firstState
          subst reached
          omega
        · have bounded := ih before reached restState
          omega

theorem mapEach_counterBound (action : α → M Symbol Guard β) (values : List α)
    (bounded : ∀ value, CounterBound (action value)) : CounterBound (mapEach action values) := by
  induction values with
  | nil => exact pure_counterBound []
  | cons first rest ih =>
      unfold mapEach
      apply counter_bind _ _ (bounded first)
      intro value
      apply counter_bind _ _ ih
      intro tail
      exact pure_counterBound (value :: tail)

theorem forEach_counterBound (action : α → M Symbol Guard Unit) (values : List α)
    (bounded : ∀ value, CounterBound (action value)) : CounterBound (forEach action values) := by
  induction values with
  | nil => exact pure_counterBound ()
  | cons first rest ih => exact counter_bind _ _ (bounded first) (fun _ => ih)

theorem setValue_counterBound (uv : Nat) (value : UVarValue Symbol) : CounterBound (setValue uv value : M Symbol Guard Unit) :=
  modify_counterBound _ (fun _ => Nat.le_succ _)

theorem rawValue_counterBound (uv : Nat) : CounterBound (rawValue uv : M Symbol Guard (UVarValue Symbol)) := by
  unfold rawValue
  apply counter_bind _ _ get_counterBound
  intro state
  cases state.values[uv]? with
  | none => exact failure_counterBound _
  | some value => exact pure_counterBound value

theorem representative_counterBound (fuel uv : Nat) : CounterBound (representative fuel uv : M Symbol Guard Nat) := by
  intro before
  unfold representative
  apply counterAt_bind _ _ before (get_counterBound before)
  intro seen middle present
  have same : (seen, middle) = (before, before) := List.mem_singleton.mp present
  have seenSame : seen = before := congrArg Prod.fst same
  have middleSame : middle = before := congrArg Prod.snd same
  subst seen
  subst middle
  cases found : UnionFind.findRoot fuel before.representatives uv with
  | none => exact failure_counterBound _ before
  | some result =>
      apply counterAt_bind _ _ before
        (set_counterAt {before with representatives := result.forest} before (Nat.le_succ _))
      intro _ after _
      exact pure_counterBound result.representative after

theorem getValue_counterBound (fuel uv : Nat) : CounterBound (getValue fuel uv : M Symbol Guard (UVarValue Symbol)) :=
  counter_bind _ _ (representative_counterBound fuel uv) rawValue_counterBound

theorem inheritAncestry_counterBound (uv : Nat) : CounterBound (inheritAncestry uv : M Symbol Guard Unit) :=
  modify_counterBound _ (fun _ => Nat.le_succ _)

theorem allocate_counterBound (node : Option Nat) : CounterBound (allocate node : M Symbol Guard Nat) := by
  intro before
  unfold allocate
  apply counterAt_bind _ _ before (get_counterBound before)
  intro seen middle present
  have same : (seen, middle) = (before, before) := List.mem_singleton.mp present
  have seenSame : seen = before := congrArg Prod.fst same
  have middleSame : middle = before := congrArg Prod.snd same
  subst seen
  subst middle
  apply counterAt_bind _ _ before
    (set_counterAt {before with counter := before.counter + 1, values := before.values ++ [UVarValue.unenumerated node []]} before (Nat.le_refl _))
  intro _ after _
  exact counter_bind _ _ (inheritAncestry_counterBound before.counter)
    (fun _ => pure_counterBound before.counter) after

theorem suspend_counterBound (trie : EqualityTrie.Trie) : CounterBound (suspend trie : M Symbol Guard Suspended) :=
  counter_bind _ _ (allocate_counterBound none) (fun uv => pure_counterBound (⟨trie, uv⟩ : Suspended))

theorem assimilate_counterBound (graph : Graph Symbol Guard) (target source : Nat) :
    CounterBound (assimilate graph target source) := by
  unfold assimilate
  split
  · exact pure_counterBound ()
  · apply counter_bind _ _ (rawValue_counterBound source)
    intro sourceValue
    cases sourceValue with
    | eliminated => exact pure_counterBound ()
    | enumerated fragment =>
        apply counter_bind _ _ (rawValue_counterBound target)
        intro _
        exact failure_counterBound _
    | unenumerated node scs =>
        apply counter_bind _ _ (rawValue_counterBound target)
        intro targetValue
        cases EnumerationState.intersectValues graph (.unenumerated node scs) targetValue with
        | none => exact failure_counterBound _
        | some merged =>
            apply counter_bind _ _ (require_counterBound _)
            intro _
            apply counter_bind _ _ (setValue_counterBound target merged)
            intro _
            apply counter_bind _ _ (setValue_counterBound source .eliminated)
            intro _
            exact modify_counterBound _ (fun _ => Nat.le_succ _)

theorem mergeNode_counterBound (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    CounterBound (mergeNode graph fuel uv node scs) := by
  unfold mergeNode
  apply counter_bind _ _ (representative_counterBound fuel uv)
  intro root
  apply counter_bind _ _ (rawValue_counterBound root)
  intro previous
  cases EnumerationState.intersectValues graph (.unenumerated (some node) scs) previous with
  | none => exact failure_counterBound _
  | some merged =>
      apply counter_bind _ _ (setValue_counterBound root merged)
      intro _
      apply counter_bind _ _ (inheritAncestry_counterBound root)
      intro _
      exact require_counterBound _

theorem unionVariables_counterBound (fuel left right : Nat) : CounterBound (unionVariables fuel left right : M Symbol Guard Unit) := by
  intro before
  unfold unionVariables
  apply counterAt_bind _ _ before (get_counterBound before)
  intro seen middle present
  have same : (seen, middle) = (before, before) := List.mem_singleton.mp present
  have seenSame : seen = before := congrArg Prod.fst same
  have middleSame : middle = before := congrArg Prod.snd same
  subst seen
  subst middle
  cases found : UnionFind.union fuel fuel before.representatives left right with
  | none => exact failure_counterBound _ before
  | some forest => exact set_counterAt {before with representatives := forest} before (Nat.le_succ _)

private theorem terminal_counterBound (graph : Graph Symbol Guard) (fuel node : Nat)
    (here below : List Suspended) (first : Suspended) (rest : List Suspended) :
    CounterBound (do
      let roots ← mapEach (fun sc => representative fuel sc.var) here
      forEach (fun sc => unionVariables fuel first.var sc.var) rest
      let root ← representative fuel first.var
      forEach (assimilate graph root) roots
      mergeNode graph fuel root node below
      EnumerationStateWorkTrace.pure (.hole root : Fragments.Fragment Symbol)) := by
  apply counter_bind _ _ (mapEach_counterBound _ _ (fun _ => representative_counterBound _ _))
  intro roots
  apply counter_bind _ _ (forEach_counterBound _ _ (fun _ => unionVariables_counterBound _ _ _))
  intro _
  apply counter_bind _ _ (representative_counterBound _ _)
  intro root
  apply counter_bind _ _ (forEach_counterBound _ _ (fun _ => assimilate_counterBound _ _ _))
  intro _
  apply counter_bind _ _ (mergeNode_counterBound _ _ _ _ _)
  intro _
  exact pure_counterBound _

private theorem node_edge_counterBound (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node, CounterBound (enumerateNode graph fuel scs node)) ∧
    (∀ scs edge, CounterBound (enumerateEdge graph fuel scs edge)) := by
  induction fuel with
  | zero => constructor <;> intros <;> exact failure_counterBound _
  | succ fuel ih =>
      constructor
      · intro scs node
        cases view : graph.node node with
        | empty =>
            simp only [enumerateNode, view]
            exact reject_counterBound
        | recursive body =>
            cases here : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil =>
                simp only [enumerateNode, view, here]
                exact counter_bind _ _ (allocate_counterBound _) (fun _ => pure_counterBound _)
            | cons first rest =>
                simp only [enumerateNode, view, here]
                exact terminal_counterBound _ _ _ _ _ _ _
        | alternatives edges =>
            cases here : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil =>
                simp only [enumerateNode, view, here]
                exact counter_bind _ _ (choose_counterBound edges) (fun edge => ih.2 scs edge)
            | cons first rest =>
                simp only [enumerateNode, view, here]
                exact terminal_counterBound _ _ _ _ _ _ _
        | unresolved missing =>
            cases here : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil =>
                simp only [enumerateNode, view, here]
                exact failure_counterBound _
            | cons first rest =>
                simp only [enumerateNode, view, here]
                exact terminal_counterBound _ _ _ _ _ _ _
      · intro scs edge
        unfold enumerateEdge
        apply counter_bind _ _ (require_counterBound _)
        intro _
        apply counter_bind _ _ (mapEach_counterBound _ _ suspend_counterBound)
        intro added
        apply counter_bind
        · apply mapEach_counterBound
          rintro ⟨child, index⟩
          exact ih.1 _ child
        · intro children
          dsimp only
          cases edge.residual with
          | none => exact counter_bind _ _ (pure_counterBound ()) (fun _ => pure_counterBound _)
          | some guard =>
              apply counter_bind
              · exact modify_counterBound _ (fun _ => Nat.le_succ _)
              · intro _
                exact pure_counterBound _

/-- Every node state satisfies the counter bound, including errors and rejection. -/
theorem enumerateNode_counterBound (graph : Graph Symbol Guard) (fuel : Nat) (scs : List Suspended) (node : Nat) :
    CounterBound (enumerateNode graph fuel scs node) := (node_edge_counterBound graph fuel).1 scs node

/-- Every edge-product state satisfies the counter bound. -/
theorem enumerateEdge_counterBound (graph : Graph Symbol Guard) (fuel : Nat) (scs : List Suspended) (edge : Edge Symbol Guard) :
    CounterBound (enumerateEdge graph fuel scs edge) := (node_edge_counterBound graph fuel).2 scs edge

/-- The selected-slot bound includes states before a rejected or failing expansion. -/
theorem enumerateOut_counterBound (graph : Graph Symbol Guard) (fuel uv : Nat) :
    CounterBound (enumerateOut graph fuel uv) := by
  unfold enumerateOut
  apply counter_bind _ _ (getValue_counterBound (fuel + 1) uv)
  intro value
  cases value with
  | eliminated | enumerated fragment => exact reject_counterBound
  | unenumerated node scs =>
      cases node with
      | none => exact reject_counterBound
      | some node =>
          apply counter_bind _ _ (representative_counterBound _ _)
          intro root
          apply counter_bind _ _ get_counterBound
          intro seen
          dsimp only
          apply counter_bind
          · exact modify_counterBound _ (fun _ => Nat.le_succ _)
          · intro _
            apply counter_bind _ _ (enumerateNode_counterBound graph fuel scs
              (match graph.node node with | .recursive body => body | _ => node))
            intro fragment
            apply counter_bind
            · exact modify_counterBound _ (fun _ => Nat.le_succ _)
            · intro _
              apply counter_bind _ _ (setValue_counterBound _ _)
              intro _
              exact pure_counterBound fragment

theorem fold_counterBound (action : α → β → M Symbol Guard α) (values : List β) (initial : α)
    (bounded : ∀ current value, CounterBound (action current value)) :
    CounterBound (EnumerationStateDriverWorkTrace.fold action values initial) := by
  induction values generalizing initial with
  | nil => exact pure_counterBound initial
  | cons first rest ih =>
      exact counter_bind _ _ (bounded initial first) (fun next => ih next)

theorem scan_counterBound (graph : Graph Symbol Guard) (fuel : Nat) (current : List Nat × List Nat)
    (entry : UVarValue Symbol × Nat) : CounterBound (EnumerationStateDriverWorkTrace.scan graph fuel current entry) := by
  rcases entry with ⟨value, index⟩
  cases value with
  | eliminated | enumerated fragment => exact pure_counterBound current
  | unenumerated node scs =>
      unfold EnumerationStateDriverWorkTrace.scan
      apply counter_bind _ _ (fold_counterBound _ _ _ ?_)
      · intro _
        exact pure_counterBound _
      · intro blocked constraint
        exact counter_bind _ _ (representative_counterBound _ _) (fun root => pure_counterBound (root :: blocked))

/-- The scheduler cap includes every representative lookup and every failed scan. -/
theorem findExpandable_counterBound (graph : Graph Symbol Guard) (fuel : Nat) :
    CounterBound (EnumerationStateDriverWorkTrace.findExpandable graph fuel) := by
  unfold EnumerationStateDriverWorkTrace.findExpandable
  apply counter_bind _ _ get_counterBound
  intro seen
  apply counter_bind _ _ (fold_counterBound _ _ _ (scan_counterBound graph fuel))
  intro current
  split <;> exact pure_counterBound _

private theorem full_counterBound (graph : Graph Symbol Guard) (order : Unit → List Nat → Option Nat)
    (fuel : Nat) (oracleState : Unit) :
    CounterBound (EnumerationStateDriverWorkTrace.enumerateFully graph order
      EnumerationStateDriverWorkTrace.noPruning fuel oracleState) := by
  induction fuel generalizing oracleState with
  | zero => exact failure_counterBound _
  | succ fuel ih =>
      unfold EnumerationStateDriverWorkTrace.enumerateFully
      apply counter_bind _ _ (findExpandable_counterBound graph (fuel + 1))
      intro offered
      cases chosen : EnumerationState.pickNext (order oracleState) offered with
      | done => exact pure_counterBound ()
      | stuck => exact reject_counterBound
      | expand uv =>
          apply counter_bind _ _ (getValue_counterBound _ _)
          intro value
          cases value with
          | eliminated | enumerated fragment => exact reject_counterBound
          | unenumerated node scs =>
              cases node with
              | none => exact reject_counterBound
              | some node =>
                  let next (repeated : Bool) : M Symbol Guard Unit :=
                    if repeated then
                      EnumerationStateDriverWorkTrace.enumerateFully graph order
                        EnumerationStateDriverWorkTrace.noPruning fuel oracleState
                    else do
                      let beforeResult ← EnumerationStateDriverWorkTrace.noPruning oracleState uv (.inr node)
                      require (!beforeResult.1)
                      let fragment ← enumerateOut graph (fuel + 1) uv
                      let afterResult ← EnumerationStateDriverWorkTrace.noPruning beforeResult.2 uv (.inl fragment)
                      require (!afterResult.1)
                      EnumerationStateDriverWorkTrace.enumerateFully graph order
                        EnumerationStateDriverWorkTrace.noPruning fuel afterResult.2
                  have nextBound : ∀ repeated, CounterBound (next repeated) := by
                    intro repeated
                    cases repeated with
                    | true => exact ih oracleState
                    | false =>
                        dsimp only [next]
                        apply counter_bind _ _ (pure_counterBound (false, oracleState))
                        intro beforeResult
                        apply counter_bind _ _ (require_counterBound _)
                        intro _
                        apply counter_bind _ _ (enumerateOut_counterBound _ _ _)
                        intro fragment
                        apply counter_bind _ _ (pure_counterBound (false, beforeResult.2))
                        intro afterResult
                        apply counter_bind _ _ (require_counterBound _)
                        intro _
                        exact ih afterResult.2
                  change CounterBound (match graph.node node with
                    | .recursive _ => do
                        let root ← representative (fuel + 1) uv
                        let current ← get
                        if EnumerationState.recursionKey node scs ∈ current.recursionAncestry root then do
                          setValue root (.unenumerated (some node) [])
                          let repeated ← EnumerationStateWorkTrace.pure true
                          next repeated
                        else do
                          let repeated ← EnumerationStateWorkTrace.pure false
                          next repeated
                    | _ => do
                        let repeated ← EnumerationStateWorkTrace.pure false
                        next repeated)
                  cases view : graph.node node with
                  | empty | alternatives edges | unresolved missing =>
                      exact counter_bind _ _ (pure_counterBound false) nextBound
                  | recursive body =>
                      apply counter_bind _ _ (representative_counterBound _ _)
                      intro root
                      apply counter_bind _ _ get_counterBound
                      intro seen
                      split
                      · exact counter_bind _ _ (setValue_counterBound _ _)
                          (fun _ => counter_bind _ _ (pure_counterBound true) nextBound)
                      · exact counter_bind _ _ (pure_counterBound false) nextBound

/-- The complete default driver bounds every recorded state by its actual total work. -/
theorem enumerateFully_counterBound (graph : Graph Symbol Guard) (order : Unit → List Nat → Option Nat) (fuel : Nat) :
    CounterBound (EnumerationStateDriverWorkTrace.enumerateFully graph order
      EnumerationStateDriverWorkTrace.noPruning fuel ()) := full_counterBound graph order fuel ()

end MicroCFTA.EnumerationStateTraceAllocationBound
