import MicroCFTA.SymbolicInternedView
import MicroCFTA.SymbolicSmartRows

/-!
# Copied row identities through smart-constructor cleanup

The source can omit a copied row when its guard is false or one copied child
is empty. This module proves exact acceptance through that cleanup. The proof
uses constructor depth. It does not assume that intersection or conditioning
already preserves languages.
-/
namespace MicroCFTA.SymbolicGraphView
open Language

/-- The two source smart-constructor reasons for removing a copied row. -/
def DropReason (target : Automaton Target Symbol) (encode : Source → Target)
    (edge : Language.Edge Source Symbol) : Prop :=
  (∀ term, edge.guard term = false) ∨ ∃ child ∈ edge.children, target (encode child) = []

/-- Copy rows, optionally remove proved empty rows, and remove duplicate identities. -/
structure NormalizedRows (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) where
  keep : Source → Language.Edge Source Symbol → Bool
  members : ∀ state edge, edge ∈ target (encode state) ↔
    ∃ original ∈ source state, keep state original = true ∧ edge = renameEdge encode original
  rejected : ∀ state edge, edge ∈ source state → keep state edge = false → DropReason target encode edge

/-- An exact copied row view is the special case that removes no rows. -/
def RowsCorrespond.normalized (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : RowsCorrespond source target encode) : NormalizedRows source target encode where
  keep _ _ := true
  members state edge := by simpa using copied state edge
  rejected _ _ _ impossible := by cases impossible

/-- A state without constructor rows accepts no finite term. -/
theorem empty_rows_reject (automaton : Automaton State Symbol) (state : State)
    (empty : automaton state = []) (term : Term Symbol) : ¬ Accepts automaton state term := by
  intro accepted
  cases accepted with
  | node edge children member _ _ => simp [empty] at member

/-- Empty-child and false-guard cleanup preserve the entire copied graph language. -/
theorem normalizedRows_exact (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : NormalizedRows source target encode)
    (state : Source) (term : Term Symbol) :
    Accepts target (encode state) term ↔ Accepts source state term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ state,
      Accepts target (encode state) term ↔ Accepts source state term) generalizing state with
  | node symbol children ih =>
    rw [accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, present, _, rfl⟩ := (copied.members state edge).mp member
      have mapped := (all₂_map_iff (Accepts target) encode original.children children).mp runs
      exact ⟨original, present, label, GraphRewrite.all₂_local_imp _ _ mapped
        (fun state term present => (ih term present state).mp), guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      have copiedRuns : All₂ (fun state term => Accepts target (encode state) term) edge.children children :=
        GraphRewrite.all₂_local_imp _ _ runs (fun state term present => (ih term present state).mpr)
      have retained : copied.keep state edge = true := by
        cases choice : copied.keep state edge with
        | true => rfl
        | false =>
          rcases copied.rejected state edge member choice with impossibleGuard | ⟨child, present, empty⟩
          · have impossible := impossibleGuard (.node symbol children)
            simp [guard] at impossible
          · obtain ⟨subtree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copiedRuns child present
            exact False.elim (empty_rows_reject target (encode child) empty subtree accepted)
      refine ⟨renameEdge encode edge, (copied.members state _).mpr ⟨edge, member, retained, rfl⟩,
        label, (all₂_map_iff (Accepts target) encode edge.children children).mpr copiedRuns, guard⟩
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member state
    rcases List.mem_cons.mp member with rfl | member
    · exact head state
    · exact tail term member state

/-- A cleaned copy cannot introduce a new structural row. -/
theorem normalizedRows_subset (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : NormalizedRows source target encode)
    (state : Source) (edge : Language.Edge Target Symbol) (member : edge ∈ target (encode state)) :
    ∃ original ∈ source state, edge = renameEdge encode original := by
  obtain ⟨original, present, _, same⟩ := (copied.members state edge).mp member
  exact ⟨original, present, same⟩

/-- The original states in the union-root construction retain their exact row view. -/
theorem union_existing_rows (automaton : Automaton State Symbol) (states : List State) :
    RowsCorrespond automaton (GraphBudget.unionGraph automaton states) some := by
  intro state edge
  simp only [GraphBudget.unionGraph, List.mem_map]
  constructor
  · rintro ⟨original, present, rfl⟩
    exact ⟨original, present, rfl⟩
  · rintro ⟨original, present, rfl⟩
    exact ⟨original, present, rfl⟩

/-- The new union root accepts exactly the combined original row language. -/
theorem union_root_exact (automaton : Automaton State Symbol) (states : List State) (term : Term Symbol) :
    Accepts (GraphBudget.unionGraph automaton states) none term ↔
      SymbolicGraph.AcceptsRows automaton (states.flatMap automaton) term := by
  cases term with
  | node symbol children =>
    rw [accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      have mapped := (all₂_map_iff (Accepts (GraphBudget.unionGraph automaton states)) some original.children children).mp runs
      exact ⟨original, present, label, mapped.imp (fun state tree accepted =>
        (rowsCorrespond_exact automaton (GraphBudget.unionGraph automaton states) some
          (union_existing_rows automaton states) state tree).mp accepted), guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      refine ⟨GraphBudget.liftEdge edge, List.mem_map.mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
      apply (all₂_map_iff (Accepts (GraphBudget.unionGraph automaton states)) some edge.children children).mpr
      exact runs.imp (fun state tree accepted =>
        (rowsCorrespond_exact automaton (GraphBudget.unionGraph automaton states) some
          (union_existing_rows automaton states) state tree).mpr accepted)

/-- Pointwise bounds on one child list bound the complete sum. -/
theorem child_sum_le (states : List State) (first second : State → Nat)
    (bounded : ∀ state ∈ states, first state ≤ second state) :
    (states.map first).sum ≤ (states.map second).sum := by
  induction states with
  | nil => exact Nat.le_refl 0
  | cons firstState rest ih =>
    have head := bounded firstState (by simp)
    have tail := ih (fun state member => bounded state (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A structural subset of copied rows cannot exceed the source graph's budget. -/
theorem structural_copy_le (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (budget : GraphBudget.Budget source) (rank : Target → Nat)
    (below : ∀ state edge, edge ∈ target state → ∀ child ∈ edge.children, rank child < rank state)
    (encode : Source → Target)
    (copied : ∀ state edge, edge ∈ target (encode state) →
      ∃ original ∈ source state, edge = renameEdge encode original)
    (state : Source) : structuralValue target rank below (encode state) ≤ budget.value state := by
  let value := structuralValue target rank below
  have loop : ∀ size state, budget.value state = size → value (encode state) ≤ budget.value state := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
      intro state same
      have each : ∀ edge ∈ target (encode state), (edge.children.map value).sum < budget.value state := by
        intro edge member
        obtain ⟨original, present, rfl⟩ := copied state edge member
        have childBounds : ∀ child ∈ original.children, value (encode child) ≤ budget.value child := by
          intro child childMember
          apply ih (budget.value child) ?_ child rfl
          rw [← same]
          exact GraphBudget.child_smaller source budget state original present child childMember
        have bounded := child_sum_le original.children (fun child => value (encode child)) budget.value childBounds
        have smaller := budget.decreases state original present
        simp only [renameEdge, List.map_map, Function.comp_def]
        omega
      have maximum := largest_le ((target (encode state)).map fun edge => (edge.children.map value).sum)
        (budget.value state - 1) (by
          intro total member
          obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
          have bound := each edge present
          omega)
      have positive := budget.positive state
      change structuralValue target rank below _ ≤ _
      rw [structuralValue_eq]
      dsimp only [value] at maximum
      omega
  exact loop (budget.value state) state rfl

/-- Product cleanup retains both structural intersection budget bounds. -/
theorem normalized_intersection_budget [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (rank : State → Nat)
    (below : ∀ state edge, edge ∈ automaton state → ∀ child ∈ edge.children, rank child < rank state)
    (meet : State → State → State)
    (copied : NormalizedRows (Language.intersect automaton automaton) automaton (fun pair => meet pair.1 pair.2))
    (left right : State) :
    structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below left ∧
      structuralValue automaton rank below (meet left right) ≤ structuralValue automaton rank below right := by
  have small := structural_copy_le (Language.intersect automaton automaton) automaton
    (GraphBudget.intersection automaton automaton (structuralBudget automaton rank below) (structuralBudget automaton rank below))
    rank below (fun pair => meet pair.1 pair.2) (normalizedRows_subset _ _ _ copied) (left, right)
  change _ ≤ min _ _ at small
  exact Nat.le_min.mp small

/-- Structural operation identities after the source smart constructors remove empty rows. -/
structure NormalizedOperationRows [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) where
  templateIdentity : Nat × Template.Pattern Symbol → Nat
  intersection : NormalizedRows
    (Language.intersect (automaton graph guard) (automaton graph guard)) (automaton graph guard)
    (fun pair => graph.intersect pair.1 pair.2)
  templates : NormalizedRows (Template.restrict (automaton graph guard)) (automaton graph guard) templateIdentity
  condition : ∀ path symbol arity root,
    graph.condition path (symbol, arity) root = templateIdentity (root, SymbolicGraph.request symbol arity path)
  projection : ∀ path root, NormalizedRows
    (GraphBudget.unionGraph (automaton graph guard) (SymbolicGraph.projectStates (automaton graph guard) path [root]))
    (automaton graph guard) (fun state => state.getD (graph.project path root))

/-- Smart-constructor product rows derive exact accepted-language intersection. -/
theorem normalized_operation_intersection [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (left right : Nat) (term : Term Symbol) :
    Accepts (automaton graph guard) (graph.intersect left right) term ↔
      Accepts (automaton graph guard) left term ∧ Accepts (automaton graph guard) right term := by
  rw [normalizedRows_exact _ _ _ view.intersection (left, right) term, accepts_intersect_iff]

/-- Smart-constructor path copies retain exactly the requested subtree constructor. -/
theorem normalized_operation_condition [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (path : List Nat) (symbol : Symbol) (arity root : Nat) (whole : Term Symbol) :
    Accepts (automaton graph guard) (graph.condition path (symbol, arity) root) whole ↔
      Accepts (automaton graph guard) root whole ∧ ∃ children,
        whole.atPath path = some (.node symbol children) ∧ children.length = arity := by
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

/-- Cleaning projected row unions cannot remove a required accepted subtree. -/
theorem normalized_operation_project [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (path : List Nat) (root : Nat) (whole part : Term Symbol)
    (accepted : Accepts (automaton graph guard) root whole) (found : whole.atPath path = some part) :
    Accepts (automaton graph guard) (graph.project path root) part := by
  have projected := SymbolicGraph.project_coverage (automaton graph guard) root path whole part accepted found
  have unionAccepted := (union_root_exact (automaton graph guard)
    (SymbolicGraph.projectStates (automaton graph guard) path [root]) part).mpr projected
  exact (normalizedRows_exact _ _ _ (view.projection path root) none part).mpr unionAccepted

/-- The actual cleaned row graph derives the source counter's complete budget. -/
def normalizedSourceBudget [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state) : SymbolicDriver.SourceBudget graph where
  value := structuralValue (automaton graph guard) rank below
  positive := (structuralBudget _ rank below).positive
  edge state edge member :=
    (structuralBudget _ rank below).decreases state ⟨edge.symbol, edge.children, guard edge⟩
      (List.mem_map.mpr ⟨edge, member, rfl⟩)
  intersection := normalized_intersection_budget _ rank below graph.intersect view.intersection

/-- Derive exact finite languages for the cleaned identity graph. -/
noncomputable def normalizedMeaning [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) : SymbolicDriver.FiniteMeaning graph where
  terms := finiteTerms (automaton graph guard) (rowBudget graph guard budget)
  distinct := finiteTerms_distinct _ _
  condition path symbol arity root whole := by
    simp only [finiteTerms_exact]
    exact normalized_operation_condition graph guard view path symbol arity root whole
  project path root whole part accepted found := by
    simp only [finiteTerms_exact] at accepted ⊢
    exact normalized_operation_project graph guard view path root whole part accepted found

/-- Independent bounded enumeration has the exact source constructor-row equation. -/
theorem finite_row_equation (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (budget : SymbolicDriver.SourceBudget graph)
    (state : Nat) (term : Term Symbol) :
    let language := finiteTerms (automaton graph guard) (rowBudget graph guard budget)
    term ∈ language state ↔ ∃ edge ∈ graph.edges state, SymbolicDriver.ShapeHolds language edge term ∧ guard edge term = true := by
  dsimp only
  rw [finiteTerms_exact]
  cases term with
  | node symbol children =>
    rw [accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, acceptedGuard⟩
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      refine ⟨original, present, ⟨children, ?_, ?_⟩, acceptedGuard⟩
      · exact congrArg (fun symbol => Term.node symbol children) label.symm
      · exact runs.imp (fun node term accepted => (finiteTerms_exact _ _ node term).mpr accepted)
    · rintro ⟨edge, member, ⟨values, equal, runs⟩, acceptedGuard⟩
      obtain ⟨rfl, rfl⟩ := Term.node.inj equal
      exact ⟨⟨edge.symbol, edge.children, guard edge⟩, List.mem_map.mpr ⟨edge, member, rfl⟩,
        rfl, runs.imp (fun node term accepted => (finiteTerms_exact _ _ node term).mp accepted), acceptedGuard⟩

/-- The complete actual index theorem permits the source's empty-row and false-guard cleanup. -/
theorem normalized_full_index [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : SymbolicDriver.Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : NormalizedOperationRows graph guard)
    (rank : Nat → Nat)
    (below : ∀ state edge, edge ∈ automaton graph guard state →
      ∀ child ∈ edge.children, rank child < rank state)
    (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (SymbolicDriver.classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let budget := normalizedSourceBudget graph guard view rank below
    let meaning := normalizedMeaning graph guard view budget
    ∃ bound, ∀ fuel, bound ≤ fuel →
      SymbolicDriver.cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      SymbolicDriver.DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, Accepts (automaton graph guard) root term →
        ∃ index : Fin (meaning.terms root).length,
          SymbolicDriver.unrank graph order fuel root index.val = .ok term ∧
          SymbolicDriver.rankOf graph order fuel root term = .ok (some index.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            SymbolicDriver.unrank graph order fuel root other.val = .ok term → other = index := by
  let budget := normalizedSourceBudget graph guard view rank below
  let meaning := normalizedMeaning graph guard view budget
  have intersection : ∀ left right term, term ∈ meaning.terms (graph.intersect left right) ↔
      term ∈ meaning.terms left ∧ term ∈ meaning.terms right := by
    intro left right term
    simp only [meaning, normalizedMeaning, finiteTerms_exact]
    exact normalized_operation_intersection graph guard view left right term
  obtain ⟨bound, correct⟩ := SymbolicDriver.rows_full_index graph order meaning budget fallback
    intersection guard compiled (finite_row_equation graph guard budget) root
  refine ⟨bound, ?_⟩
  intro fuel enough
  obtain ⟨count, total, bijection⟩ := correct fuel enough
  refine ⟨count, total, ?_⟩
  intro term accepted
  exact bijection term ((finiteTerms_exact _ _ root term).mpr accepted)

end MicroCFTA.SymbolicGraphView
