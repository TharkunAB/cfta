import MicroCFTA.SymbolicNormalizedRows

/-!
# Closed self-intersection and copied product rows

The source returns a closed operand when both intersection identities are
equal. This shortcut omits nonempty cross rows. It is a separate case, not
empty-row cleanup. Other pairs use constructor product rows and the source
smart-constructor cleanup.
-/
namespace MicroCFTA.SymbolicGraphView
open Language

/-- The source's closed self-intersection shortcut and ordinary product branch. -/
structure ProductRows [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (meet : State → State → State) where
  diagonal : ∀ state, meet state state = state
  keep : State → State → Language.Edge (State × State) Symbol → Bool
  members : ∀ left right, left ≠ right → ∀ edge, edge ∈ automaton (meet left right) ↔
    ∃ original ∈ Language.intersect automaton automaton (left, right),
      keep left right original = true ∧ edge = renameEdge (fun pair => meet pair.1 pair.2) original
  rejected : ∀ left right, left ≠ right → ∀ edge,
    edge ∈ Language.intersect automaton automaton (left, right) → keep left right edge = false →
      DropReason automaton (fun pair => meet pair.1 pair.2) edge

/-- The explicit self shortcut and cleaned product rows derive exact intersection. -/
theorem productRows_exact [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (meet : State → State → State) (view : ProductRows automaton meet)
    (left right : State) (term : Term Symbol) :
    Accepts automaton (meet left right) term ↔ Accepts automaton left term ∧ Accepts automaton right term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ left right,
      Accepts automaton (meet left right) term ↔ Accepts automaton left term ∧ Accepts automaton right term)
    generalizing left right with
  | node symbol children ih =>
    by_cases same : left = right
    · subst right
      rw [view.diagonal]
      exact ⟨fun accepted => ⟨accepted, accepted⟩, And.left⟩
    · rw [← accepts_intersect_iff automaton automaton left right, accepts_node_iff, accepts_node_iff]
      have childExact : ∀ tree ∈ children, ∀ pair : State × State,
          Accepts automaton (meet pair.1 pair.2) tree ↔
            Accepts (Language.intersect automaton automaton) pair tree := by
        intro tree member pair
        rw [accepts_intersect_iff]
        exact ih tree member pair.1 pair.2
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        obtain ⟨original, present, _, rfl⟩ := (view.members left right same edge).mp member
        have mapped := (all₂_map_iff (Accepts automaton) (fun pair : State × State => meet pair.1 pair.2)
          original.children children).mp runs
        exact ⟨original, present, label, GraphRewrite.all₂_local_imp _ _ mapped
          (fun pair tree member => (childExact tree member pair).mp), guard⟩
      · rintro ⟨edge, member, label, runs, guard⟩
        have copiedRuns : All₂ (fun pair tree => Accepts automaton (meet pair.1 pair.2) tree) edge.children children :=
          GraphRewrite.all₂_local_imp _ _ runs (fun pair tree member => (childExact tree member pair).mpr)
        have retained : view.keep left right edge = true := by
          cases choice : view.keep left right edge with
          | true => rfl
          | false =>
            rcases view.rejected left right same edge member choice with impossibleGuard | ⟨child, present, empty⟩
            · have impossible := impossibleGuard (.node symbol children)
              simp [guard] at impossible
            · obtain ⟨subtree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copiedRuns child present
              exact False.elim (empty_rows_reject automaton (meet child.1 child.2) empty subtree accepted)
        refine ⟨renameEdge (fun pair => meet pair.1 pair.2) edge,
          (view.members left right same _).mpr ⟨edge, member, retained, rfl⟩, label, ?_, guard⟩
        exact (all₂_map_iff (Accepts automaton) (fun pair : State × State => meet pair.1 pair.2)
          edge.children children).mpr copiedRuns
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member left right
    rcases List.mem_cons.mp member with rfl | member
    · exact head left right
    · exact tail term member left right

/-- Self-intersection is nonincreasing, and every other product row retains both bounds. -/
theorem productRows_budget [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state)
    (meet : State → State → State) (view : ProductRows automaton meet) (left right : State) :
    structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below left ∧
      structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below right := by
  let value := structuralValue automaton rank below
  have loop : ∀ height left, rank left = height → ∀ right,
      value (meet left right) ≤ value left ∧ value (meet left right) ≤ value right := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro left ranked right
      by_cases same : left = right
      · subst right
        rw [view.diagonal]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · have each : ∀ edge ∈ automaton (meet left right),
            (edge.children.map value).sum ≤ largest ((automaton left).map fun edge => (edge.children.map value).sum) ∧
            (edge.children.map value).sum ≤ largest ((automaton right).map fun edge => (edge.children.map value).sum) := by
          intro edge present
          obtain ⟨original, member, _, rfl⟩ := (view.members left right same edge).mp present
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

/-- Constructor-graph operation views with the actual closed self shortcut. -/
structure ClosedOperationRows [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) where
  intersection : ProductRows (automaton graph guard) graph.intersect
  templateIdentity : Nat × Template.Pattern Symbol → Nat
  templates : NormalizedRows (Template.restrict (automaton graph guard)) (automaton graph guard) templateIdentity
  condition : ∀ path symbol arity root,
    graph.condition path (symbol, arity) root = templateIdentity (root, SymbolicGraph.request symbol arity path)
  projection : ∀ path root, NormalizedRows
    (GraphBudget.unionGraph (automaton graph guard) (SymbolicGraph.projectStates (automaton graph guard) path [root]))
    (automaton graph guard) (fun state => state.getD (graph.project path root))

/-- Derive the full termination budget from the actual closed product branches. -/
def closedSourceBudget [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : ClosedOperationRows graph guard)
    (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state) : SymbolicDriver.SourceBudget graph where
  value := structuralValue (automaton graph guard) rank below
  positive := (structuralBudget _ rank below).positive
  edge state edge member :=
    (structuralBudget _ rank below).decreases state ⟨edge.symbol, edge.children, guard edge⟩
      (List.mem_map.mpr ⟨edge, member, rfl⟩)
  intersection := productRows_budget _ rank below graph.intersect view.intersection

/-- Constructor copies and projected row unions derive the decoder's complete finite meaning. -/
noncomputable def closedMeaning [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : ClosedOperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) : SymbolicDriver.FiniteMeaning graph where
  terms := finiteTerms (automaton graph guard) (rowBudget graph guard budget)
  distinct := finiteTerms_distinct _ _
  condition path symbol arity root whole := by
    simp only [finiteTerms_exact]
    rw [view.condition, normalizedRows_exact _ _ _ view.templates,
      Template.restrict_exact, SymbolicGraph.request_matches]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨subtree, found, shape⟩
      cases subtree with
      | node actual children =>
        obtain ⟨rfl, length⟩ := shape
        exact ⟨children, found, length⟩
    · rintro ⟨children, found, length⟩
      exact ⟨.node symbol children, found, rfl, length⟩
  project path root whole part accepted found := by
    simp only [finiteTerms_exact] at accepted ⊢
    have projected := SymbolicGraph.project_coverage (automaton graph guard) root path whole part accepted found
    have unionAccepted := (union_root_exact (automaton graph guard)
      (SymbolicGraph.projectStates (automaton graph guard) path [root]) part).mpr projected
    exact (normalizedRows_exact _ _ _ (view.projection path root) none part).mpr unionAccepted

/-- Closed constructor graphs have exact complete indexing after smart cleanup and self-intersection. -/
theorem closed_full_index [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : SymbolicDriver.Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : ClosedOperationRows graph guard)
    (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state)
    (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (SymbolicDriver.classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let budget := closedSourceBudget graph guard view rank below
    let meaning := closedMeaning graph guard view budget
    ∃ bound, ∀ fuel, bound ≤ fuel →
      SymbolicDriver.cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      SymbolicDriver.DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, Accepts (automaton graph guard) root term →
        ∃ index : Fin (meaning.terms root).length,
          SymbolicDriver.unrank graph order fuel root index.val = .ok term ∧
          SymbolicDriver.rankOf graph order fuel root term = .ok (some index.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            SymbolicDriver.unrank graph order fuel root other.val = .ok term → other = index := by
  let budget := closedSourceBudget graph guard view rank below
  let meaning := closedMeaning graph guard view budget
  have intersection : ∀ left right term, term ∈ meaning.terms (graph.intersect left right) ↔
      term ∈ meaning.terms left ∧ term ∈ meaning.terms right := by
    intro left right term
    simp only [meaning, closedMeaning, finiteTerms_exact]
    exact productRows_exact _ _ view.intersection left right term
  obtain ⟨bound, correct⟩ := SymbolicDriver.rows_full_index graph order meaning budget fallback
    intersection guard compiled (finite_row_equation graph guard budget) root
  refine ⟨bound, ?_⟩
  intro fuel enough
  obtain ⟨count, total, bijection⟩ := correct fuel enough
  refine ⟨count, total, ?_⟩
  intro term accepted
  exact bijection term ((finiteTerms_exact _ _ root term).mpr accepted)

end MicroCFTA.SymbolicGraphView
