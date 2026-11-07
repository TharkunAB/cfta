import MicroCFTA.EnumerationStateAllocation

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateExpansionBounds

open EnumerationState

variable {Symbol Guard α β : Type}

local instance : Monad List where
  pure := fun value => List.cons value List.nil
  bind := fun branches next => List.flatMap next branches

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

private theorem mapM_cons_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (action : α → m β) (first : α) (rest : List α) :
    (first :: rest).mapM action =
      (do let value ← action first; let tail ← rest.mapM action; pure (value :: tail)) := by
  simp

private def Within (cost : Nat) (before after : EnumerationState.State Symbol Guard) : Prop :=
  before.counter ≤ after.counter ∧ after.counter ≤ before.counter + cost ∧
    after.values.length + before.counter = before.values.length + after.counter

private def Budgeted (cost : Nat) (action : EnumerateM Symbol Guard α) : Prop :=
  ∀ before value after, Except.ok (value, after) ∈ ExceptT.run (action before) → Within cost before after

private theorem within_refl (state : EnumerationState.State Symbol Guard) : Within 0 state state := by
  constructor
  · exact Nat.le_refl _
  constructor
  · exact Nat.le_refl _
  · rfl

private theorem within_mono (h : Within lower before after) (larger : lower ≤ upper) :
    Within upper before after := by
  rcases h with ⟨monotone, bounded, offset⟩
  exact ⟨monotone, by omega, offset⟩

private theorem within_trans (first : Within left before middle)
    (second : Within right middle after) : Within (left + right) before after := by
  rcases first with ⟨_, _, _⟩
  rcases second with ⟨_, _, _⟩
  constructor
  · omega
  constructor <;> omega

private theorem budgeted_mono (h : Budgeted lower action) (larger : lower ≤ upper) :
    Budgeted upper action := by
  intro before value after run
  exact within_mono (h before value after run) larger

private theorem pure_budget (value : α) :
    Budgeted 0 (pure value : EnumerateM Symbol Guard α) := by
  intro before result after run
  change Except.ok (result, after) ∈ [Except.ok (value, before)] at run
  have same := List.mem_singleton.mp run
  cases same
  exact within_refl before

private theorem mem_bind (first : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β)
    (before : EnumerationState.State Symbol Guard) (value : β)
    (after : EnumerationState.State Symbol Guard) :
    Except.ok (value, after) ∈ ExceptT.run ((first >>= next) before) ↔
      ∃ result middle, Except.ok (result, middle) ∈ ExceptT.run (first before) ∧
        Except.ok (value, after) ∈ ExceptT.run (next result middle) := by
  dsimp [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run]
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨item, member, run⟩
    cases item with
    | error error => simp [ExceptT.bindCont, Pure.pure] at run
    | ok pair => exact ⟨pair.1, pair.2, member, run⟩
  · rintro ⟨result, middle, member, run⟩
    exact ⟨.ok (result, middle), member, run⟩

private theorem bind_budget (first : Budgeted left action)
    (rest : ∀ value, Budgeted right (next value)) :
    Budgeted (left + right) (action >>= next) := by
  intro before value after run
  obtain ⟨result, middle, firstRun, secondRun⟩ := (mem_bind _ _ _ _ _).mp run
  exact within_trans (first before result middle firstRun) (rest result middle value after secondRun)

private theorem bind_zero_left (first : Budgeted 0 action)
    (rest : ∀ value, Budgeted cost (next value)) : Budgeted cost (action >>= next) := by
  simpa only [Nat.zero_add] using bind_budget first rest

private theorem bind_zero_right (first : Budgeted cost action)
    (rest : ∀ value, Budgeted 0 (next value)) : Budgeted cost (action >>= next) := by
  exact bind_budget first rest

/-- Add the costs of all operations in a list. -/
def totalCost (cost : α → Nat) : List α → Nat
  | [] => 0
  | first :: rest => cost first + totalCost cost rest

/-- Bound the cost of any selected operation in a list. -/
def maxCost (cost : α → Nat) : List α → Nat
  | [] => 0
  | first :: rest => max (cost first) (maxCost cost rest)

private theorem cost_le_max (member : value ∈ values) : cost value ≤ maxCost cost values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst value
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

private theorem mapM_budget (values : List α) (action : α → EnumerateM Symbol Guard β)
    (cost : α → Nat) (bounded : ∀ value, Budgeted (cost value) (action value)) :
    Budgeted (totalCost cost values) (values.mapM action) := by
  induction values with
  | nil => exact pure_budget []
  | cons first rest ih =>
      rw [mapM_cons_eq]
      change Budgeted (cost first + totalCost cost rest)
        (do let value ← action first; let tail ← rest.mapM action; pure (value :: tail))
      exact bind_budget (bounded first) (fun value =>
        bind_zero_right ih (fun tail => pure_budget (value :: tail)))

private theorem forM_zero_budget (values : List α)
    (action : α → EnumerateM Symbol Guard PUnit) (bounded : ∀ value, Budgeted 0 (action value)) :
    Budgeted 0 (values.forM action) := by
  induction values with
  | nil => exact pure_budget ()
  | cons first rest ih =>
      change Budgeted 0 (do action first; rest.forM action)
      exact bind_zero_left (bounded first) (fun _ => ih)

private theorem reject_budget : Budgeted cost (EnumerationState.reject : EnumerateM Symbol Guard α) := by
  intro before value after run
  cases run

private theorem failure_budget (error : EnumerationState.Error) :
    Budgeted cost (EnumerationState.failure error : EnumerateM Symbol Guard α) := by
  intro before value after run
  change Except.ok (value, after) ∈ [Except.error error] at run
  simp at run

private theorem require_budget (condition : Bool) :
    Budgeted 0 (EnumerationState.require condition : EnumerateM Symbol Guard Unit) := by
  cases condition
  · exact reject_budget
  · exact pure_budget ()

private theorem get_budget : Budgeted 0 (get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) := by
  intro before value after run
  change Except.ok (value, after) ∈ [Except.ok (before, before)] at run
  have same := List.mem_singleton.mp run
  cases same
  exact within_refl before

private theorem modify_budget (update : EnumerationState.State Symbol Guard → EnumerationState.State Symbol Guard)
    (counter : ∀ state, (update state).counter = state.counter)
    (length : ∀ state, (update state).values.length = state.values.length) :
    Budgeted 0 (modify update : EnumerateM Symbol Guard Unit) := by
  intro before value after run
  change Except.ok (value, after) ∈ [Except.ok ((), update before)] at run
  have same := List.mem_singleton.mp run
  cases same
  dsimp [Within]
  rw [counter, length]
  exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩

private theorem choose_bind_budget (values : List α) (action : α → EnumerateM Symbol Guard β)
    (cost : α → Nat) (bounded : ∀ value, value ∈ values → Budgeted (cost value) (action value)) :
    Budgeted (maxCost cost values) (EnumerationState.choose values >>= action) := by
  intro before value after run
  obtain ⟨chosen, middle, selected, rest⟩ := (mem_bind _ _ _ _ _).mp run
  obtain ⟨element, member, same⟩ := List.mem_map.mp selected
  have pairEqual : (element, before) = (chosen, middle) := Except.ok.inj same
  cases pairEqual
  exact within_mono (bounded _ member before value after rest) (cost_le_max member)

private theorem allocate_budget (node : Option Nat) :
    Budgeted 1 (EnumerationState.allocate node : EnumerateM Symbol Guard Nat) := by
  intro before value after run
  obtain ⟨next, execution, counter, length, _, _, _⟩ :=
    EnumerationStateAllocation.allocate_frame before node
  rw [execution] at run
  have same := List.mem_singleton.mp run
  cases same
  dsimp [Within]
  rw [counter, length]
  constructor
  · omega
  constructor <;> omega

private theorem suspend_budget (trie : EqualityTrie.Trie) :
    Budgeted 1 (EnumerationState.suspend trie : EnumerateM Symbol Guard Suspended) := by
  unfold EnumerationState.suspend
  exact bind_zero_right (allocate_budget none) (fun _ => pure_budget _)

private theorem setValue_budget (key : Nat) (value : UVarValue Symbol) :
    Budgeted 0 (EnumerationState.setValue key value : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.setValue
  apply modify_budget
  · intro state
    rfl
  · intro state
    simp

private theorem inherit_budget (key : Nat) :
    Budgeted 0 (EnumerationState.inheritAncestry key : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.inheritAncestry
  apply modify_budget <;> intro state <;> rfl

private theorem rawValue_budget (key : Nat) :
    Budgeted 0 (EnumerationState.rawValue key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.rawValue
  apply bind_zero_left get_budget
  intro state
  split
  · exact failure_budget _
  · exact pure_budget _

private theorem get_bind_budget
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (bounded : ∀ before value after,
      Except.ok (value, after) ∈ ExceptT.run (next before before) → Within cost before after) :
    Budgeted cost ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  intro before value after run
  obtain ⟨state, middle, got, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (state, middle) ∈ [Except.ok (before, before)] at got
  have paired := Except.ok.inj (List.mem_singleton.mp got)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact bounded _ value after continued

private theorem representative_budget (fuel key : Nat) :
    Budgeted 0 (EnumerationState.representative fuel key : EnumerateM Symbol Guard Nat) := by
  unfold EnumerationState.representative
  apply get_bind_budget
  intro before value after run
  cases search : UnionFind.findRoot fuel before.representatives key with
  | none =>
      simp only [search] at run
      exact failure_budget _ before value after run
  | some found =>
      simp only [search] at run
      change Except.ok (value, after) ∈ [Except.ok (found.representative, _)] at run
      have pairEqual := Except.ok.inj (List.mem_singleton.mp run)
      have stateEqual := congrArg Prod.snd pairEqual
      dsimp only at stateEqual
      subst after
      exact within_refl before

private theorem unionVariables_budget (fuel left right : Nat) :
    Budgeted 0 (EnumerationState.unionVariables fuel left right : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.unionVariables
  apply get_bind_budget
  intro before value after run
  cases united : UnionFind.union fuel fuel before.representatives left right with
  | none =>
      simp only [united] at run
      exact failure_budget _ before value after run
  | some forest =>
      simp only [united] at run
      change Except.ok (value, after) ∈ [Except.ok ((), _)] at run
      have pairEqual := Except.ok.inj (List.mem_singleton.mp run)
      have stateEqual := congrArg Prod.snd pairEqual
      dsimp only at stateEqual
      subst after
      exact within_refl before

private theorem assimilate_budget (graph : Graph Symbol Guard) (target source : Nat) :
    Budgeted 0 (EnumerationState.assimilate graph target source) := by
  unfold EnumerationState.assimilate
  split
  · exact pure_budget ()
  · apply bind_zero_left (rawValue_budget source)
    intro sourceValue
    cases sourceValue
    case eliminated => exact pure_budget ()
    all_goals
      apply bind_zero_left (rawValue_budget target)
      intro targetValue
      split
      · exact failure_budget _
      · apply bind_zero_left (require_budget _)
        intro _
        apply bind_zero_left (setValue_budget _ _)
        intro _
        apply bind_zero_left (setValue_budget _ _)
        intro _
        apply modify_budget <;> intro state <;> rfl

private theorem mergeNode_budget (graph : Graph Symbol Guard) (fuel key node : Nat)
    (scs : List Suspended) : Budgeted 0 (EnumerationState.mergeNode graph fuel key node scs) := by
  unfold EnumerationState.mergeNode
  apply bind_zero_left (representative_budget fuel key)
  intro root
  apply bind_zero_left (rawValue_budget root)
  intro previous
  split
  · exact failure_budget _
  · apply bind_zero_left (setValue_budget _ _)
    intro _
    apply bind_zero_left (inherit_budget root)
    intro _
    exact require_budget _

private theorem totalCost_one (values : List α) : totalCost (fun _ => 1) values = values.length := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [totalCost, ih, Nat.add_comm]

private theorem totalCost_zero (values : List α) : totalCost (fun _ => 0) values = 0 := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [totalCost, ih]

private theorem mapM_zero_budget (values : List α) (action : α → EnumerateM Symbol Guard β)
    (bounded : ∀ value, Budgeted 0 (action value)) : Budgeted 0 (values.mapM action) := by
  simpa only [totalCost_zero] using mapM_budget values action (fun _ => 0) bounded

private theorem suspensions_budget (tries : List EqualityTrie.Trie) :
    Budgeted tries.length (tries.mapM EnumerationState.suspend : EnumerateM Symbol Guard (List Suspended)) := by
  simpa only [totalCost_one] using mapM_budget tries EnumerationState.suspend (fun _ => 1) suspend_budget

mutual
  /-- Bound allocations in an actual node expansion at the supplied fuel. -/
  def nodeAllocationBudget (graph : Graph Symbol Guard) (fuel node : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | remaining + 1 =>
      match graph.node node with
      | .recursive _ => 1
      | .alternatives edges => maxCost (edgeAllocationBudget graph remaining) edges
      | _ => 0
  termination_by fuel
  decreasing_by all_goals omega

  /-- Bound suspension allocations and all recursive child expansions. -/
  def edgeAllocationBudget (graph : Graph Symbol Guard) (fuel : Nat) (edge : Edge Symbol Guard) : Nat :=
    match fuel with
    | 0 => 0
    | remaining + 1 => edge.equalities.length +
      totalCost (fun child : Nat × Nat => nodeAllocationBudget graph remaining child.1)
        edge.children.zipIdx
  termination_by fuel
  decreasing_by all_goals omega
end

private theorem terminal_node_budget (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended)
    (present : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) ≠ []) :
    Budgeted 0 (EnumerationState.enumerateNode graph (fuel + 1) scs node) := by
  cases selected : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
  | nil => exact False.elim (present selected)
  | cons first rest =>
      cases view : graph.node node <;>
        simp only [EnumerationState.enumerateNode, view, selected]
      case empty => exact reject_budget
      all_goals
        apply bind_zero_left (mapM_zero_budget _ _ (fun _ => representative_budget _ _))
        intro roots
        apply bind_zero_left (forM_zero_budget _ _ (fun _ => unionVariables_budget _ _ _))
        intro _
        apply bind_zero_left (representative_budget _ _)
        intro root
        apply bind_zero_left (forM_zero_budget _ _ (fun _ => assimilate_budget _ _ _))
        intro _
        apply bind_zero_left (mergeNode_budget _ _ _ _ _)
        intro _
        exact pure_budget _

private theorem expansion_budget (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node, Budgeted (nodeAllocationBudget graph fuel node)
      (EnumerationState.enumerateNode graph fuel scs node)) ∧
    (∀ scs edge, Budgeted (edgeAllocationBudget graph fuel edge)
      (EnumerationState.enumerateEdge graph fuel scs edge)) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node
        exact failure_budget _
      · intro scs edge
        exact failure_budget _
  | succ fuel ih =>
      obtain ⟨nodeIH, edgeIH⟩ := ih
      constructor
      · intro scs node
        by_cases absent : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = []
        · cases view : graph.node node with
          | empty =>
              simp only [nodeAllocationBudget, EnumerationState.enumerateNode, view]
              exact reject_budget
          | unresolved reference =>
              simp only [nodeAllocationBudget, EnumerationState.enumerateNode, view, absent]
              exact failure_budget _
          | recursive body =>
              simp only [nodeAllocationBudget, EnumerationState.enumerateNode, view, absent]
              exact bind_zero_right (allocate_budget _) (fun _ => pure_budget _)
          | alternatives edges =>
              simp only [nodeAllocationBudget, EnumerationState.enumerateNode, view, absent]
              exact choose_bind_budget edges _ (edgeAllocationBudget graph fuel)
                (fun edge _ => edgeIH scs edge)
        · exact budgeted_mono (terminal_node_budget graph fuel node scs absent) (Nat.zero_le _)
      · intro scs edge
        simp only [edgeAllocationBudget, EnumerationState.enumerateEdge]
        apply bind_zero_left (require_budget _)
        intro _
        apply bind_budget (suspensions_budget edge.equalities)
        intro added
        apply bind_zero_right
        · exact mapM_budget _ _
            (fun child : Nat × Nat => nodeAllocationBudget graph fuel child.1)
            (fun _ => nodeIH _ _)
        · intro children
          split
          · exact pure_budget _
          · apply bind_zero_left
            · apply modify_budget <;> intro state <;> rfl
            · intro _
              exact pure_budget _

/-- Bound counter growth and preserve the value-count offset on successful returns. -/
theorem enumerateNode_counter_bounds (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (before : EnumerationState.State Symbol Guard)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateNode graph fuel scs node before)) :
    before.counter ≤ after.counter ∧
      after.counter ≤ before.counter + nodeAllocationBudget graph fuel node ∧
      after.values.length + before.counter = before.values.length + after.counter := by
  exact (expansion_budget graph fuel).1 scs node before fragment after returned

/-- Bound edge suspensions and child growth on successful returns. -/
theorem enumerateEdge_counter_bounds (graph : Graph Symbol Guard) (fuel : Nat)
    (edge : Edge Symbol Guard) (scs : List Suspended)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateEdge graph fuel scs edge before)) :
    before.counter ≤ after.counter ∧
      after.counter ≤ before.counter + edgeAllocationBudget graph fuel edge ∧
      after.values.length + before.counter = before.values.length + after.counter := by
  exact (expansion_budget graph fuel).2 scs edge before fragment after returned

/-- A successful node expansion preserves agreement between value count and counter. -/
theorem enumerateNode_preserves_shape (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (before : EnumerationState.State Symbol Guard)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (shape : before.values.length = before.counter)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateNode graph fuel scs node before)) :
    after.values.length = after.counter := by
  have preserved := (enumerateNode_counter_bounds graph fuel node scs before fragment after returned).2.2
  omega

/-- A successful edge expansion preserves agreement between value count and counter. -/
theorem enumerateEdge_preserves_shape (graph : Graph Symbol Guard) (fuel : Nat)
    (edge : Edge Symbol Guard) (scs : List Suspended)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard) (shape : before.values.length = before.counter)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateEdge graph fuel scs edge before)) :
    after.values.length = after.counter := by
  have preserved := (enumerateEdge_counter_bounds graph fuel edge scs before fragment after returned).2.2
  omega

end MicroCFTA.EnumerationStateExpansionBounds
