import MicroCFTA.SymbolicComplete
import MicroCFTA.GraphBudget
import MicroCFTA.GraphRewrite

/-!
# Graph identity views for complete symbolic indexing

The independent accepted language is obtained from constructor rows. A
structural budget gives a finite enumeration bound. Identity-producing graph
operations are checked by their copied rows, not by assumed language laws.
-/
namespace MicroCFTA.SymbolicGraphView
open Language

/-- Copy a row and replace only its child identities. -/
def renameEdge (encode : Source → Target) (edge : Language.Edge Source Symbol) :
    Language.Edge Target Symbol :=
  ⟨edge.label, edge.children.map encode, edge.guard⟩

/-- Reading a copied identity gives the same rows, up to duplicate removal and order. -/
def RowsCorrespond (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) : Prop :=
  ∀ state edge, edge ∈ target (encode state) ↔
    ∃ original ∈ source state, edge = renameEdge encode original

/-- Replacing source identities commutes with the ordered child relation. -/
theorem all₂_map_iff (relation : Target → Value → Prop) (encode : Source → Target)
    (states : List Source) (values : List Value) :
    All₂ relation (states.map encode) values ↔ All₂ (fun state value => relation (encode state) value) states values := by
  induction states generalizing values with
  | nil => constructor <;> intro runs <;> cases runs <;> exact .nil
  | cons first rest ih =>
    constructor
    · intro runs
      cases runs with
      | cons head tail => exact .cons head ((ih _).mp tail)
    · intro runs
      cases runs with
      | cons head tail => exact .cons head ((ih _).mpr tail)

/-- Exact copied rows preserve finite acceptance, without an injective-key premise. -/
theorem rowsCorrespond_exact (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : RowsCorrespond source target encode)
    (state : Source) (term : Term Symbol) :
    Accepts target (encode state) term ↔ Accepts source state term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ state,
      Accepts target (encode state) term ↔ Accepts source state term) generalizing state with
  | node symbol children ih =>
    rw [accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, present, rfl⟩ := (copied state edge).mp member
      have mapped := (all₂_map_iff (Accepts target) encode original.children children).mp runs
      exact ⟨original, present, label, GraphRewrite.all₂_local_imp _ _ mapped
        (fun state term present => (ih term present state).mp), guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      refine ⟨renameEdge encode edge, (copied state _).mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
      apply (all₂_map_iff (Accepts target) encode edge.children children).mpr
      exact GraphRewrite.all₂_local_imp _ _ runs (fun state term present => (ih term present state).mpr)
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member state
    rcases List.mem_cons.mp member with rfl | member
    · exact head state
    · exact tail term member state

/-- Interpret the source edge records as explicit guarded constructor rows. -/
def automaton (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) : Automaton Nat Symbol :=
  fun state => (graph.edges state).map fun edge => ⟨edge.symbol, edge.children, guard edge⟩

/-- The source structural edge budget is also a budget on the explicit row view. -/
def rowBudget (graph : SymbolicDriver.Graph Symbol) (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool)
    (budget : SymbolicDriver.SourceBudget graph) : GraphBudget.Budget (automaton graph guard) where
  value := budget.value
  positive := budget.positive
  decreases state edge member := by
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact budget.edge state original present

/-- Each finite accepted term is bounded by the structural budget of its root. -/
theorem accepts_height (automaton : Automaton State Symbol) (budget : GraphBudget.Budget automaton)
    (state : State) (term : Term Symbol) (accepted : Accepts automaton state term) :
    term.height ≤ budget.value state := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => forestHeight terms ≤ (states.map budget.value).sum) with
  | node edge children member runs guard ih =>
    have smaller := budget.decreases _ edge member
    simp only [Term.height, forestHeight] at ih ⊢
    omega
  | nil => exact Nat.le_refl 0
  | cons head tail headBound tailBound =>
    simp only [forestHeight] at tailBound
    simp only [forestHeight, List.foldr_cons, List.map_cons, List.sum_cons]
    apply Nat.max_le.mpr
    exact ⟨by omega, by omega⟩

/-- A structural row budget gives a complete finite list of distinct accepted terms. -/
noncomputable def finiteTerms (automaton : Automaton State Symbol) (budget : GraphBudget.Budget automaton)
    (state : State) : List (Term Symbol) := by
  classical
  exact (enumerate automaton (budget.value state) state).eraseDups

/-- The finite list is independent of accepting-run multiplicity. -/
theorem finiteTerms_distinct (automaton : Automaton State Symbol) (budget : GraphBudget.Budget automaton)
    (state : State) : (finiteTerms automaton budget state).Nodup := by
  classical
  exact SymbolicDriver.eraseDups_nodup _

/-- The budget-derived list has all and only the finite accepted terms. -/
theorem finiteTerms_exact (automaton : Automaton State Symbol) (budget : GraphBudget.Budget automaton)
    (state : State) (term : Term Symbol) :
    term ∈ finiteTerms automaton budget state ↔ Accepts automaton state term := by
  classical
  simp only [finiteTerms, List.mem_eraseDups, mem_enumerate_iff]
  exact ⟨And.left, fun accepted => ⟨accepted, accepts_height automaton budget state term accepted⟩⟩

/-- Structural identities for synchronous product, path copies, and projected row unions. -/
structure OperationRows [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) where
  templateIdentity : Nat × Template.Pattern Symbol → Nat
  intersection : RowsCorrespond
    (Language.intersect (automaton graph guard) (automaton graph guard)) (automaton graph guard)
    (fun pair => graph.intersect pair.1 pair.2)
  templates : RowsCorrespond (Template.restrict (automaton graph guard)) (automaton graph guard) templateIdentity
  condition : ∀ path symbol arity root,
    graph.condition path (symbol, arity) root = templateIdentity (root, SymbolicGraph.request symbol arity path)
  projection : ∀ path root edge,
    edge ∈ automaton graph guard (graph.project path root) ↔
      edge ∈ SymbolicGraph.projectRows (automaton graph guard) path root

/-- Synchronous product row identities imply exact accepted-language intersection. -/
theorem operation_intersection [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (left right : Nat) (term : Term Symbol) :
    Accepts (automaton graph guard) (graph.intersect left right) term ↔
      Accepts (automaton graph guard) left term ∧ Accepts (automaton graph guard) right term := by
  rw [rowsCorrespond_exact _ _ _ view.intersection (left, right) term, accepts_intersect_iff]

/-- Path-copy row identities imply exact constructor-conditioned acceptance. -/
theorem operation_condition [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (path : List Nat) (symbol : Symbol) (arity root : Nat) (whole : Term Symbol) :
    Accepts (automaton graph guard) (graph.condition path (symbol, arity) root) whole ↔
      Accepts (automaton graph guard) root whole ∧ ∃ children,
        whole.atPath path = some (.node symbol children) ∧ children.length = arity := by
  rw [view.condition, rowsCorrespond_exact _ _ _ view.templates,
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

/-- Projected row identities include every existing accepted subtree. -/
theorem operation_project [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (path : List Nat) (root : Nat) (whole part : Term Symbol)
    (accepted : Accepts (automaton graph guard) root whole) (found : whole.atPath path = some part) :
    Accepts (automaton graph guard) (graph.project path root) part := by
  have projected := SymbolicGraph.project_coverage (automaton graph guard) root path whole part accepted found
  cases part with
  | node symbol children =>
    obtain ⟨edge, member, label, runs, acceptedGuard⟩ := projected
    exact (accepts_node_iff _ _ _ _).mpr
      ⟨edge, (view.projection path root edge).mpr member, label, runs, acceptedGuard⟩

/-- Derive the decoder's complete finite meaning from structural graph data. -/
noncomputable def finiteMeaning [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) : SymbolicDriver.FiniteMeaning graph where
  terms := finiteTerms (automaton graph guard) (rowBudget graph guard budget)
  distinct := finiteTerms_distinct _ _
  condition path symbol arity root whole := by
    simp only [finiteTerms_exact]
    exact operation_condition graph guard view path symbol arity root whole
  project path root whole part accepted found := by
    simp only [finiteTerms_exact] at accepted ⊢
    exact operation_project graph guard view path root whole part accepted found

/-- The finite meaning has exact child-domain intersection by copied product rows. -/
theorem finiteMeaning_intersection [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) (left right : Nat) (term : Term Symbol) :
    term ∈ (finiteMeaning graph guard view budget).terms (graph.intersect left right) ↔
      term ∈ (finiteMeaning graph guard view budget).terms left ∧
      term ∈ (finiteMeaning graph guard view budget).terms right := by
  simp only [finiteMeaning, finiteTerms_exact]
  exact operation_intersection graph guard view left right term

/-- Constructor membership in the finite meaning is exactly one guarded source row. -/
theorem finiteMeaning_rows [DecidableEq Symbol] (graph : SymbolicDriver.Graph Symbol)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) (state : Nat) (term : Term Symbol) :
    term ∈ (finiteMeaning graph guard view budget).terms state ↔
      ∃ edge ∈ graph.edges state,
        SymbolicDriver.ShapeHolds (finiteMeaning graph guard view budget).terms edge term ∧ guard edge term = true := by
  simp only [finiteMeaning, finiteTerms_exact]
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

/-- Structural graph views discharge all semantic graph premises of the complete source index. -/
theorem view_full_index [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : SymbolicDriver.Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : OperationRows graph guard)
    (budget : SymbolicDriver.SourceBudget graph) (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (SymbolicDriver.classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let meaning := finiteMeaning graph guard view budget
    ∃ bound, ∀ fuel, bound ≤ fuel →
      SymbolicDriver.cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      SymbolicDriver.DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, Accepts (automaton graph guard) root term →
        ∃ rank : Fin (meaning.terms root).length,
          SymbolicDriver.unrank graph order fuel root rank.val = .ok term ∧
          SymbolicDriver.rankOf graph order fuel root term = .ok (some rank.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            SymbolicDriver.unrank graph order fuel root other.val = .ok term → other = rank := by
  let meaning := finiteMeaning graph guard view budget
  obtain ⟨bound, correct⟩ := SymbolicDriver.rows_full_index graph order meaning budget fallback
    (finiteMeaning_intersection graph guard view budget) guard compiled (finiteMeaning_rows graph guard view budget) root
  refine ⟨bound, ?_⟩
  intro fuel enough
  obtain ⟨count, total, bijection⟩ := correct fuel enough
  refine ⟨count, total, ?_⟩
  intro term accepted
  exact bijection term ((finiteTerms_exact _ _ root term).mpr accepted)

end MicroCFTA.SymbolicGraphView
