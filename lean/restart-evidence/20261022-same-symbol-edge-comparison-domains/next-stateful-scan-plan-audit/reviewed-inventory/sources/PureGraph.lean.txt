import MicroCFTA.SymbolicGraph
import MicroCFTA.RedundantEdges

/-!
# Whole-graph preservation from constructor rows

Every graph transition consumes one constructor. Thus local row equivalence
under the original child languages implies global equivalence, even when the
graph has cycles. No coinductive acceptance or epsilon step is assumed here.
-/
namespace MicroCFTA.GraphRewrite
open Language SymbolicGraph

/-- Change a child-run relation using a theorem for every actual child term. -/
theorem all₂_local_imp (before after : State → Term Symbol → Prop)
    {states : List State} {terms : List (Term Symbol)} (runs : All₂ before states terms)
    (change : ∀ state term, term ∈ terms → before state term → after state term) :
    All₂ after states terms := by
  induction runs with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (change _ _ (by simp) head) (ih (fun state term member => change state term (by simp [member])))

/-- Exact local row replacement preserves the complete finite-term language. -/
theorem rows_preserve_language (before after : Automaton State Symbol)
    (rowMeaning : ∀ state term, AcceptsRows before (after state) term ↔ Accepts before state term)
    (state : State) (term : Term Symbol) : Accepts after state term ↔ Accepts before state term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ state, Accepts after state term ↔ Accepts before state term)
    generalizing state with
  | node symbol children ih =>
    rw [← rowMeaning state (.node symbol children), accepts_node_iff]
    change (∃ edge ∈ after state, edge.label = symbol ∧
      All₂ (Accepts after) edge.children children ∧ edge.guard (.node symbol children) = true) ↔ _
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      exact ⟨edge, member, label, all₂_local_imp _ _ runs
        (fun state term present => (ih term present state).mp), guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      exact ⟨edge, member, label, all₂_local_imp _ _ runs
        (fun state term present => (ih term present state).mpr), guard⟩
  | nil => simp_all
  | cons first rest hf hr =>
    rename_i term member state
    rcases List.mem_cons.mp member with rfl | member
    · exact hf state
    · exact hr term member state

/-- Interpret the terms of one interned edge identity in its original graph. -/
def edgeMeaning (automaton : Automaton State Symbol) (edgeOf : Identity → Edge State Symbol)
    (identity : Identity) (term : Term Symbol) : Prop := AcceptsRows automaton [edgeOf identity] term

/-- Reading interned edge identities changes no root-row language. -/
theorem identity_rows (automaton : Automaton State Symbol) (edgeOf : Identity → Edge State Symbol)
    (identities : List Identity) (term : Term Symbol) :
    AcceptsRows automaton (identities.map edgeOf) term ↔
      RedundantEdges.Denotes (edgeMeaning automaton edgeOf) identities term := by
  cases term with
  | node symbol children =>
    simp only [AcceptsRows, RedundantEdges.Denotes, edgeMeaning, List.mem_map, List.mem_singleton]
    constructor
    · rintro ⟨edge, ⟨identity, member, rfl⟩, label, runs, guard⟩
      exact ⟨identity, member, edgeOf identity, rfl, label, runs, guard⟩
    · rintro ⟨identity, member, edge, rfl, label, runs, guard⟩
      exact ⟨edgeOf identity, ⟨identity, member, rfl⟩, label, runs, guard⟩

/-- Removing redundant identity alternatives at every state preserves cyclic graph languages. -/
theorem reduce_graph_exact [DecidableEq Identity] (rows : State → List Identity)
    (edgeOf : Identity → Edge State Symbol) (meet : Identity → Identity → Identity)
    (intersection : ∀ first second term,
      edgeMeaning (fun state => (rows state).map edgeOf) edgeOf (meet first second) term ↔
        edgeMeaning (fun state => (rows state).map edgeOf) edgeOf first term ∧
        edgeMeaning (fun state => (rows state).map edgeOf) edgeOf second term)
    (state : State) (term : Term Symbol) :
    Accepts (fun state => (RedundantEdges.reduce meet (rows state)).map edgeOf) state term ↔
      Accepts (fun state => (rows state).map edgeOf) state term := by
  apply rows_preserve_language
  intro selected tree
  rw [identity_rows, RedundantEdges.reduce_exact meet _ intersection, ← identity_rows]
  cases tree with
  | node symbol children =>
    simpa only [AcceptsRows] using (accepts_node_iff (fun state => (rows state).map edgeOf) selected symbol children).symm

end MicroCFTA.GraphRewrite
