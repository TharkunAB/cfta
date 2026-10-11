import MicroCFTA.SymbolicGraphView

/-!
# Structural budgets from acyclic graph identities

Each identity has a topological rank. Its budget is one plus the greatest
sum of child budgets among its constructor rows. Duplicate rows do not change
this value. Copied synchronous products have no greater budget than either
input. No accepted-language or counting premise is used.
-/
namespace MicroCFTA.SymbolicGraphView
open Language

/-- The largest natural entry, with zero for an empty list. -/
def largest : List Nat → Nat
  | [] => 0
  | first :: rest => max first (largest rest)

/-- An actual entry is bounded by the largest entry. -/
theorem largest_member (values : List Nat) (value : Nat) (present : value ∈ values) : value ≤ largest values := by
  induction values with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

/-- A bound on every entry bounds the maximum, including an empty list. -/
theorem largest_le (values : List Nat) (bound : Nat) (bounded : ∀ value ∈ values, value ≤ bound) :
    largest values ≤ bound := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
    exact Nat.max_le.mpr ⟨bounded first (by simp), ih (fun value present => bounded value (by simp [present]))⟩

/-- The sum of child budgets is strictly below the recursively computed parent budget. -/
def structuralValue (automaton : Automaton State Symbol) (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state)
    (state : State) : Nat :=
  largest ((automaton state).attach.map fun edge =>
    (edge.val.children.attach.map fun child => structuralValue automaton rank below child.val).sum) + 1
termination_by rank state
decreasing_by exact below state edge.val edge.property child.val child.property

/-- The budget equation removes proof attachments from the executable row data. -/
theorem structuralValue_eq (automaton : Automaton State Symbol) (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state)
    (state : State) :
    structuralValue automaton rank below state =
      largest ((automaton state).map fun edge => (edge.children.map (structuralValue automaton rank below)).sum) + 1 := by
  rw [structuralValue]
  simp

/-- Topological ranks derive a complete structural row budget. -/
def structuralBudget (automaton : Automaton State Symbol) (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state) :
    GraphBudget.Budget automaton where
  value := structuralValue automaton rank below
  positive state := by rw [structuralValue_eq]; omega
  decreases state edge member := by
    rw [structuralValue_eq]
    have bound := largest_member ((automaton state).map fun edge =>
      (edge.children.map (structuralValue automaton rank below)).sum) _ (List.mem_map.mpr ⟨edge, member, rfl⟩)
    omega

/-- Pointwise paired bounds imply bounds on both complete child sums. -/
theorem zip_sum_le (left : List Left) (right : List Right)
    (value : Left → Right → Nat) (a : Left → Nat) (b : Right → Nat)
    (bounded : ∀ x ∈ left, ∀ y ∈ right, value x y ≤ a x ∧ value x y ≤ b y) :
    ((left.zip right).map fun pair => value pair.1 pair.2).sum ≤ (left.map a).sum ∧
      ((left.zip right).map fun pair => value pair.1 pair.2).sum ≤ (right.map b).sum := by
  induction left generalizing right with
  | nil => simp
  | cons first rest ih =>
    cases right with
    | nil => simp
    | cons second tail =>
      have head := bounded first (by simp) second (by simp)
      have remaining := ih tail (fun x member y present => bounded x (by simp [member]) y (by simp [present]))
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega⟩

/-- Copied product rows derive both intersection budget bounds. -/
theorem structural_intersection [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state)
    (meet : State → State → State)
    (copied : RowsCorrespond (Language.intersect automaton automaton) automaton (fun pair => meet pair.1 pair.2))
    (left right : State) :
    structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below left ∧
      structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below right := by
  let value := structuralValue automaton rank below
  have loop : ∀ height left, rank left = height → ∀ right,
      value (meet left right) ≤ value left ∧ value (meet left right) ≤ value right := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro left ranked right
      have each : ∀ edge ∈ automaton (meet left right),
          (edge.children.map value).sum ≤ largest ((automaton left).map fun edge => (edge.children.map value).sum) ∧
          (edge.children.map value).sum ≤ largest ((automaton right).map fun edge => (edge.children.map value).sum) := by
        intro edge present
        obtain ⟨original, member, rfl⟩ := (copied (left, right) edge).mp present
        obtain ⟨first, firstMember, second, secondMember, _, _, rfl⟩ :=
          (mem_intersect_iff automaton automaton left right original).mp member
        have sums := zip_sum_le first.children second.children (fun a b => value (meet a b)) value value (by
          intro child childMember other _
          apply ih (rank child) ?_ child rfl other
          rw [← ranked]
          exact below left first firstMember child childMember)
        have leftBound := largest_member ((automaton left).map fun edge => (edge.children.map value).sum)
          _ (List.mem_map.mpr ⟨first, firstMember, rfl⟩)
        have rightBound := largest_member ((automaton right).map fun edge => (edge.children.map value).sum)
          _ (List.mem_map.mpr ⟨second, secondMember, rfl⟩)
        simp only [renameEdge, List.map_map, Function.comp_def]
        exact ⟨Nat.le_trans sums.1 leftBound, Nat.le_trans sums.2 rightBound⟩
      have first := largest_le ((automaton (meet left right)).map fun edge => (edge.children.map value).sum)
        (largest ((automaton left).map fun edge => (edge.children.map value).sum)) (by
          intro total member
          obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
          exact (each edge present).1)
      have second := largest_le ((automaton (meet left right)).map fun edge => (edge.children.map value).sum)
        (largest ((automaton right).map fun edge => (edge.children.map value).sum)) (by
          intro total member
          obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
          exact (each edge present).2)
      change structuralValue automaton rank below _ ≤ structuralValue automaton rank below _ ∧
        structuralValue automaton rank below _ ≤ structuralValue automaton rank below _
      rw [structuralValue_eq automaton rank below (meet left right),
        structuralValue_eq automaton rank below left, structuralValue_eq automaton rank below right]
      dsimp only [value] at first second
      exact ⟨by omega, by omega⟩
  exact loop (rank left) left rfl right

/-- Acyclic rows and copied product identities derive the full source termination budget. -/
def sourceBudget [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool)
    (view : OperationRows graph guard) (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state) : SymbolicDriver.SourceBudget graph where
  value := structuralValue (automaton graph guard) rank below
  positive := (structuralBudget _ rank below).positive
  edge state edge member :=
    (structuralBudget _ rank below).decreases state ⟨edge.symbol, edge.children, guard edge⟩
      (List.mem_map.mpr ⟨edge, member, rfl⟩)
  intersection := structural_intersection _ rank below graph.intersect view.intersection

/-- A validated acyclic graph view has exact complete indexing, with no semantic operation premises. -/
theorem acyclic_full_index [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : SymbolicDriver.Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state)
    (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (SymbolicDriver.classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let budget := sourceBudget graph guard view rank below
    let meaning := finiteMeaning graph guard view budget
    ∃ bound, ∀ fuel, bound ≤ fuel →
      SymbolicDriver.cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      SymbolicDriver.DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, Accepts (automaton graph guard) root term →
        ∃ index : Fin (meaning.terms root).length,
          SymbolicDriver.unrank graph order fuel root index.val = .ok term ∧
          SymbolicDriver.rankOf graph order fuel root term = .ok (some index.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            SymbolicDriver.unrank graph order fuel root other.val = .ok term → other = index :=
  view_full_index graph order guard view (sourceBudget graph guard view rank below) fallback compiled root

end MicroCFTA.SymbolicGraphView
