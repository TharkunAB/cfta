import MicroCFTA.EnumerationConstructors
import MicroCFTA.SymbolicHashJoin

/-!
# Constructor-row intersection for enumeration

The source joins equal constructor labels, checks equal arity, intersects
ordered child pairs, and conjoins their guards. The node constructor removes
false guards and empty children. These row operations derive the semantic
intersection premise of the exact enumeration theorem.
-/

namespace MicroCFTA.EnumerationIntersection
open Language SymbolicGraphView EnumerationState EnumerationSemantics EnumerationCorrectness

/-- One constructor pair retains both guards and intersects each ordered child pair. -/
def joinedEdge (meet : Nat → Nat → Nat) (first second : Language.Edge Nat Symbol) : Language.Edge Nat Symbol :=
  ⟨first.label, (first.children.zip second.children).map (fun pair => meet pair.1 pair.2),
    fun term => first.guard term && second.guard term⟩

/-- The source joins equal symbols and rejects unequal child counts. -/
def joinedRows [DecidableEq Symbol] (meet : Nat → Nat → Nat)
    (left right : List (Language.Edge Nat Symbol)) : List (Language.Edge Nat Symbol) :=
  (SymbolicHashJoin.hashJoin Language.Edge.label Prod.mk left right).flatMap fun pair =>
    if pair.1.children.length = pair.2.children.length then [joinedEdge meet pair.1 pair.2] else []

/-- The hash join emits exactly the copied guarded-product rows. -/
theorem joinedRows_member [DecidableEq Symbol] (automaton : Automaton Nat Symbol) (meet : Nat → Nat → Nat)
    (left right : Nat) (edge : Language.Edge Nat Symbol) :
    edge ∈ joinedRows meet (automaton left) (automaton right) ↔
      ∃ original ∈ Language.intersect automaton automaton (left, right),
        edge = renameEdge (fun pair => meet pair.1 pair.2) original := by
  simp only [joinedRows, List.mem_flatMap]
  constructor
  · rintro ⟨pair, pairMember, edgeMember⟩
    obtain ⟨first, firstMember, second, secondMember, label, pairSame⟩ :=
      (SymbolicHashJoin.hashJoin_member Language.Edge.label Prod.mk _ _ pair).mp pairMember
    subst pair
    split at edgeMember
    · rename_i arity
      have same := List.mem_singleton.mp edgeMember
      subst edge
      refine ⟨⟨first.label, first.children.zip second.children, fun term => first.guard term && second.guard term⟩, ?_, rfl⟩
      exact (Language.mem_intersect_iff automaton automaton left right _).mpr
        ⟨first, firstMember, second, secondMember, label, arity, rfl⟩
    · simp at edgeMember
  · rintro ⟨original, present, rfl⟩
    obtain ⟨first, firstMember, second, secondMember, label, arity, rfl⟩ :=
      (Language.mem_intersect_iff automaton automaton left right original).mp present
    refine ⟨(first, second), ?_, ?_⟩
    · exact (SymbolicHashJoin.hashJoin_member Language.Edge.label Prod.mk _ _ _).mpr
        ⟨first, firstMember, second, secondMember, label, rfl⟩
    · simp [arity, joinedEdge, renameEdge]

/-- Concrete readback of the closed shortcut, hash join, and node cleanup. -/
structure HashRows [DecidableEq Symbol] (automaton : Automaton Nat Symbol) (meet : Nat → Nat → Nat) where
  empty : Nat
  emptyRows : automaton empty = []
  diagonal : ∀ state, meet state state = state
  dead : Nat → Nat → Language.Edge Nat Symbol → Bool
  dead_correct : ∀ left right edge, edge ∈ joinedRows meet (automaton left) (automaton right) →
    dead left right edge = true → ∀ term, edge.guard term = false
  members : ∀ left right, left ≠ right → ∀ edge, edge ∈ automaton (meet left right) ↔
    edge ∈ (joinedRows meet (automaton left) (automaton right)).filter
      (fun edge => !dead left right edge && !edge.children.contains empty)

/-- Row readback derives the product interface, including the two exact removal reasons. -/
def HashRows.product [DecidableEq Symbol] (automaton : Automaton Nat Symbol) (meet : Nat → Nat → Nat)
    (rows : HashRows automaton meet) : ProductRows automaton meet where
  diagonal := rows.diagonal
  keep left right original :=
    let copied := renameEdge (fun pair => meet pair.1 pair.2) original
    !rows.dead left right copied && !copied.children.contains rows.empty
  members left right different edge := by
    rw [rows.members left right different, List.mem_filter, joinedRows_member]
    constructor
    · rintro ⟨⟨original, member, rfl⟩, kept⟩
      exact ⟨original, member, kept, rfl⟩
    · rintro ⟨original, member, kept, rfl⟩
      exact ⟨⟨original, member, rfl⟩, kept⟩
  rejected left right _ original member rejected := by
    let copied := renameEdge (fun pair => meet pair.1 pair.2) original
    have present : copied ∈ joinedRows meet (automaton left) (automaton right) :=
      (joinedRows_member automaton meet left right copied).mpr ⟨original, member, rfl⟩
    change (!rows.dead left right copied && !copied.children.contains rows.empty) = false at rejected
    by_cases dead : rows.dead left right copied = true
    · exact Or.inl (rows.dead_correct left right copied present dead)
    · have emptyMember : rows.empty ∈ copied.children := by
        simpa [dead] using rejected
      obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp emptyMember
      exact Or.inr ⟨pair, pairMember, by simpa only [same] using rows.emptyRows⟩

/-- The actual constructor operations supply the enumerator's intersection law. -/
theorem intersection_correct [DecidableEq Symbol] (graph : Graph Symbol Guard)
    (meaning : Guard → Term Symbol → Prop) (complete : CompleteGraph graph)
    (rows : HashRows (EnumerationLanguage.automaton graph meaning) graph.intersect) :
    IntersectionCorrect graph (Accepted graph meaning) := by
  intro left right term
  simp only [EnumerationLanguage.accepted_iff graph meaning complete]
  exact productRows_exact _ _ (rows.product _ _) left right term

/-- Constructor readback and checked row operations give exact initialized enumeration. -/
theorem runs_exact [DecidableEq Symbol] (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (empty : Nat)
    (constructors : ∀ node, graph.node node = .empty ∨ ∃ edges, graph.node node = .alternatives edges)
    (built : ∀ node edges, graph.node node = .alternatives edges → EnumerationConstructors.SourceRows empty edges)
    (rows : HashRows (EnumerationLanguage.automaton graph meaning) graph.intersect)
    (marker : Symbol) (root : Nat) (term : Term Symbol) :
    Accepted graph meaning root term ↔ ∃ fuel pending after,
      .ok ((term, pending), after) ∈ runs graph marker fuel root ∧ ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  have complete := EnumerationConstructors.complete_of_readback graph empty constructors built
  exact EnumerationExact.runs_exact graph meaning complete (intersection_correct graph meaning complete rows) marker root term

end MicroCFTA.EnumerationIntersection
