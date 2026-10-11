import MicroCFTA.SymbolicGraph

/-!
# Structural budgets for symbolic graph operations

Budgets include every structural transition, before guard evaluation. A graph
with a finite topological rank has such a budget. Intersection and path
conditioning preserve budgets without inspecting accepted terms.
-/
namespace MicroCFTA.GraphBudget
open Language Template SymbolicGraph

/-- A positive bound larger than the complete child tuple of every row. -/
structure Budget (automaton : Automaton State Symbol) where
  value : State → Nat
  positive : ∀ state, 0 < value state
  decreases : ∀ state edge, edge ∈ automaton state → (edge.children.map value).sum < value state

/-- Pointwise natural bounds also bound their finite sum. -/
theorem sum_bound (values : List α) (measure : α → Nat) (bound : Nat)
    (each : ∀ value ∈ values, measure value ≤ bound) :
    (values.map measure).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons first rest ih =>
    have head := each first (by simp)
    have tail := ih (fun value member => each value (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- A finite topological rank gives a budget even when every guard rejects. -/
def ofRank (automaton : Automaton State Symbol) (rank : State → Nat) (width : Nat)
    (arity : ∀ state edge, edge ∈ automaton state → edge.children.length ≤ width)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state) :
    Budget automaton where
  value state := (width + 1) ^ (rank state + 1)
  positive _ := Nat.pow_pos (by omega)
  decreases state edge member := by
    have capPositive : 0 < (width + 1) ^ rank state := Nat.pow_pos (by omega)
    calc
      (edge.children.map (fun child => (width + 1) ^ (rank child + 1))).sum ≤
          edge.children.length * (width + 1) ^ rank state :=
        sum_bound _ _ _ (fun child present => Nat.pow_le_pow_right (by omega)
          (by have smaller := below state edge member child present; omega))
      _ ≤ width * (width + 1) ^ rank state := Nat.mul_le_mul_right _ (arity state edge member)
      _ < (width + 1) * (width + 1) ^ rank state := by rw [Nat.succ_mul]; omega
      _ = (width + 1) ^ (rank state + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- A paired minimum never exceeds the total budget of either side. -/
theorem zip_min_bound (left : List α) (right : List β) (f : α → Nat) (g : β → Nat) :
    ((left.zip right).map fun pair => min (f pair.1) (g pair.2)).sum ≤ (left.map f).sum ∧
    ((left.zip right).map fun pair => min (f pair.1) (g pair.2)).sum ≤ (right.map g).sum := by
  induction left generalizing right with
  | nil => simp
  | cons first rest ih => cases right with
    | nil => simp
    | cons second tail =>
      have bound := ih tail
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      have l := Nat.min_le_left (f first) (g second)
      have r := Nat.min_le_right (f first) (g second)
      omega

/-- Synchronous intersection has a budget no larger than either input. -/
def intersection [DecidableEq Symbol] (left : Automaton Q Symbol) (right : Automaton R Symbol)
    (a : Budget left) (b : Budget right) : Budget (Language.intersect left right) where
  value pair := min (a.value pair.1) (b.value pair.2)
  positive pair := by have := a.positive pair.1; have := b.positive pair.2; omega
  decreases pair edge member := by
    obtain ⟨first, firstMember, second, secondMember, _, _, rfl⟩ :=
      (mem_intersect_iff left right pair.1 pair.2 edge).mp member
    have sums := zip_min_bound first.children second.children a.value b.value
    have firstBound := a.decreases pair.1 first firstMember
    have secondBound := b.decreases pair.2 second secondMember
    change ((first.children.zip second.children).map fun pair => min (a.value pair.1) (b.value pair.2)).sum < _
    omega

/-- Child-template pairing retains the complete original child budget. -/
theorem zip_left_sum (left : List α) (right : List β) (measure : α → Nat)
    (length : left.length = right.length) :
    ((left.zip right).map fun pair => measure pair.1).sum = (left.map measure).sum := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons first rest ih => cases right with
    | nil => simp at length
    | cons second tail =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at length
      simp [ih tail length]

/-- Every template copy uses the budget of its original state. -/
def restriction [DecidableEq Symbol] (automaton : Automaton State Symbol) (budget : Budget automaton) :
    Budget (Template.restrict automaton) where
  value pair := budget.value pair.1
  positive pair := budget.positive pair.1
  decreases pair edge member := by
    obtain ⟨original, present, patterns, aligned, rfl⟩ :=
      (Template.mem_restrict_iff automaton pair.1 pair.2 edge).mp member
    have length := (childTemplates_length pair.2 original.label original.children.length patterns aligned).symm
    change ((original.children.zip patterns).map fun pair => budget.value pair.1).sum < _
    rw [zip_left_sum original.children patterns budget.value length]
    exact budget.decreases pair.1 original present

/-- A constructor-conditioned copy does not increase the original state's budget. -/
theorem condition_no_growth [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (budget : Budget automaton) (state : State) (symbol : Symbol) (arity : Nat) (path : List Nat) :
    (restriction automaton budget).value (state, request symbol arity path) = budget.value state := rfl

/-- Every natural list entry is bounded by the complete sum. -/
theorem member_le_sum (values : List Nat) (value : Nat) (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have tail := ih member
      simp only [List.sum_cons]
      omega

/-- Any individual child is strictly smaller than its parent. -/
theorem child_smaller (automaton : Automaton State Symbol) (budget : Budget automaton)
    (state : State) (edge : Edge State Symbol) (present : edge ∈ automaton state)
    (child : State) (member : child ∈ edge.children) : budget.value child < budget.value state := by
  have inSum : budget.value child ∈ edge.children.map budget.value := List.mem_map.mpr ⟨child, member, rfl⟩
  have lower := member_le_sum _ _ inSum
  have upper := budget.decreases state edge present
  omega

/-- The source projection worker retains the bound of its input states. -/
theorem project_bound [DecidableEq State] (automaton : Automaton State Symbol) (budget : Budget automaton)
    (path : List Nat) (states : List State) (bound : Nat)
    (bounded : ∀ state ∈ states, budget.value state ≤ bound) :
    ∀ state ∈ projectStates automaton path states, budget.value state ≤ bound := by
  induction path generalizing states with
  | nil => exact bounded
  | cons index rest ih =>
    apply ih
    intro child member
    simp only [List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap] at member
    obtain ⟨edge, ⟨state, stateMember, edgeMember⟩, found⟩ := member
    have small := child_smaller automaton budget state edge edgeMember child (List.mem_of_getElem? found)
    have big := bounded state stateMember
    omega

/-- Existing projected states at a proper path have strictly smaller budgets. -/
theorem project_smaller [DecidableEq State] (automaton : Automaton State Symbol) (budget : Budget automaton)
    (root : State) (index : Nat) (rest : List Nat) (state : State)
    (present : state ∈ projectStates automaton (index :: rest) [root]) : budget.value state < budget.value root := by
  have bound : budget.value state ≤ budget.value root - 1 := by
    apply project_bound automaton budget rest _ (budget.value root - 1) ?_ state present
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_eraseDups, List.mem_filterMap] at member
    obtain ⟨edge, edgeMember, found⟩ := member
    have small := child_smaller automaton budget root edge edgeMember child (List.mem_of_getElem? found)
    omega
  have positive := budget.positive root
  omega

/-- The maximum projected budget includes one for an empty row union. -/
def maximum (measure : State → Nat) : List State → Nat
  | [] => 1
  | state :: rest => max (measure state) (maximum measure rest)

/-- A row-union budget is always positive, including an empty union. -/
theorem maximum_positive (measure : State → Nat) (states : List State) : 0 < maximum measure states := by
  induction states with
  | nil => simp [maximum]
  | cons state rest ih => simp only [maximum]; omega

/-- Each source state's budget is below the row-union maximum. -/
theorem maximum_member (measure : State → Nat) (states : List State) (state : State)
    (member : state ∈ states) : measure state ≤ maximum measure states := by
  induction states with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- A common bound bounds the complete row union. -/
theorem maximum_le (measure : State → Nat) (states : List State) (bound : Nat)
    (positive : 1 ≤ bound) (each : ∀ state ∈ states, measure state ≤ bound) : maximum measure states ≤ bound := by
  induction states with
  | nil => exact positive
  | cons state rest ih =>
    have head := each state (by simp)
    have tail := ih (fun state member => each state (by simp [member]))
    simp only [maximum]
    omega

/-- A strict common bound is retained by a row union when its empty budget also fits. -/
theorem maximum_lt (measure : State → Nat) (states : List State) (bound : Nat)
    (positive : 1 < bound) (each : ∀ state ∈ states, measure state < bound) : maximum measure states < bound := by
  induction states with
  | nil => exact positive
  | cons state rest ih =>
    have head := each state (by simp)
    have tail := ih (fun state member => each state (by simp [member]))
    simp only [maximum]
    omega

/-- Lift an original edge into the graph with one new union root. -/
def liftEdge (edge : Edge State Symbol) : Edge (Option State) Symbol :=
  ⟨edge.label, edge.children.map some, edge.guard⟩

/-- Row union with all original child states preserved. -/
def unionGraph (automaton : Automaton State Symbol) (states : List State) : Automaton (Option State) Symbol
  | none => (states.flatMap automaton).map liftEdge
  | some state => (automaton state).map liftEdge

/-- Row union has the maximum source budget and preserves all child budget decreases. -/
def union (automaton : Automaton State Symbol) (budget : Budget automaton) (states : List State) :
    Budget (unionGraph automaton states) where
  value | none => maximum budget.value states | some state => budget.value state
  positive | none => maximum_positive budget.value states | some state => budget.positive state
  decreases state edge member := by
    cases state with
    | none =>
      obtain ⟨original, source, rfl⟩ := List.mem_map.mp member
      obtain ⟨owner, ownerMember, present⟩ := List.mem_flatMap.mp source
      have lower := budget.decreases owner original present
      have upper := maximum_member budget.value states owner ownerMember
      simp only [liftEdge, List.map_map, Function.comp_def]
      change (original.children.map budget.value).sum < maximum budget.value states
      omega
    | some state =>
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      simpa [liftEdge, List.map_map, Function.comp_def] using budget.decreases state original present

/-- Projecting any path cannot increase the union root's structural budget. -/
theorem projection_no_growth [DecidableEq State] (automaton : Automaton State Symbol)
    (budget : Budget automaton) (root : State) (path : List Nat) :
    (union automaton budget (projectStates automaton path [root])).value none ≤ budget.value root := by
  apply maximum_le
  · exact budget.positive root
  · exact project_bound automaton budget path [root] (budget.value root) (by simp)

/-- A nonempty proper projection has a strictly smaller union-root budget. -/
theorem projection_decreases [DecidableEq State] (automaton : Automaton State Symbol)
    (budget : Budget automaton) (root : State) (index : Nat) (rest : List Nat)
    (nonempty : projectStates automaton (index :: rest) [root] ≠ []) :
    (union automaton budget (projectStates automaton (index :: rest) [root])).value none < budget.value root := by
  have witness : ∃ state, state ∈ projectStates automaton (index :: rest) [root] :=
    List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨state, present⟩ := witness
  have lower := budget.positive state
  have upper := project_smaller automaton budget root index rest state present
  apply maximum_lt
  · omega
  · exact project_smaller automaton budget root index rest

end MicroCFTA.GraphBudget
