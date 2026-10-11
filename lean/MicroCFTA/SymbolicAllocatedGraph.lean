import MicroCFTA.SymbolicHashJoin

/-!
# Allocation histories supply the symbolic graph rank

Every constructor key refers to previously issued child identities. A finite
history records reservations and first-writer installations. Different graph
rows may be read after different finite histories. Their allocation order
still supplies one global topological rank for the symbolic graph interface.
-/
namespace MicroCFTA.SymbolicInternedView
open Language Cache SymbolicGraphView

/-- An interning step with the constructor key's child references checked. -/
inductive ConstructorStep [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol)) :
    Cache.State Key → Cache.State Key → Prop where
  | reserve (state : Cache.State Key) (key : Key) (children : ChildrenIssued shape state key) :
      ConstructorStep shape state (Cache.reserve state key).2
  | install (state : Cache.State Key) (candidate : Cache.Interned Key)
      (issued : state.issued candidate.identity = some candidate.key) :
      ConstructorStep shape state (Cache.install state candidate)

/-- A finite interleaving of constructor reservations and canonical installations. -/
inductive ConstructorHistory [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol)) :
    Cache.State Key → Cache.State Key → Prop where
  | refl (state : Cache.State Key) : ConstructorHistory shape state state
  | step (history : ConstructorHistory shape initial before) (next : ConstructorStep shape before after) :
      ConstructorHistory shape initial after

/-- Every permitted constructor step preserves canonical allocation and acyclic child references. -/
theorem constructorStep_valid [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (before after : Cache.State Key) (step : ConstructorStep shape before after)
    (valid : Cache.Valid before) (acyclic : Acyclic shape before) :
    Cache.Valid after ∧ Acyclic shape after := by
  cases step with
  | reserve key children =>
    exact ⟨Cache.reserve_valid before key valid, reserve_acyclic shape before valid acyclic key children⟩
  | install candidate issued =>
    exact ⟨Cache.install_valid before candidate valid issued, install_acyclic shape before candidate acyclic⟩

/-- Any finite constructor history retains both cache and graph invariants. -/
theorem constructorHistory_valid [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (initial finalState : Cache.State Key) (history : ConstructorHistory shape initial finalState)
    (valid : Cache.Valid initial) (acyclic : Acyclic shape initial) :
    Cache.Valid finalState ∧ Acyclic shape finalState := by
  induction history with
  | refl => exact ⟨valid, acyclic⟩
  | step _ next ih => exact constructorStep_valid shape _ _ next ih.1 ih.2

/-- Each observed row has a finite allocation history and its immutable issued key. -/
def AllocatedRows [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (automaton : Automaton Nat Symbol) : Prop :=
  ∀ identity edge, edge ∈ automaton identity →
    ∃ snapshot key, ConstructorHistory shape Cache.emptyState snapshot ∧
      snapshot.issued identity = some key ∧ edge ∈ shape key

/-- Local finite allocation histories derive one topological rank for all observed rows. -/
theorem allocated_rank [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (automaton : Automaton Nat Symbol) (allocated : AllocatedRows shape automaton)
    (identity : Nat) (edge : Language.Edge Nat Symbol) (member : edge ∈ automaton identity)
    (child : Nat) (present : child ∈ edge.children) : child < identity := by
  obtain ⟨snapshot, key, history, issued, row⟩ := allocated identity edge member
  have acyclic := (constructorHistory_valid shape Cache.emptyState snapshot history Cache.empty_valid (empty_acyclic shape)).2
  exact (acyclic identity key issued edge row child present).1

/-- Complete indexing follows from copied source rows, compiled guards, and ordinary allocation histories. -/
theorem allocated_full_index [DecidableEq Key] [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (shape : Key → List (Language.Edge Nat Symbol)) (graph : SymbolicDriver.Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : ClosedOperationRows graph guard)
    (allocated : AllocatedRows shape (automaton graph guard)) (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (SymbolicDriver.classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let budget := closedSourceBudget graph guard view id (allocated_rank shape _ allocated)
    let meaning := closedMeaning graph guard view budget
    ∃ bound, ∀ fuel, bound ≤ fuel →
      SymbolicDriver.cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      SymbolicDriver.DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, Accepts (automaton graph guard) root term →
        ∃ index : Fin (meaning.terms root).length,
          SymbolicDriver.unrank graph order fuel root index.val = .ok term ∧
          SymbolicDriver.rankOf graph order fuel root term = .ok (some index.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            SymbolicDriver.unrank graph order fuel root other.val = .ok term → other = index :=
  closed_full_index graph order guard view id (allocated_rank shape _ allocated) fallback compiled root

end MicroCFTA.SymbolicInternedView
