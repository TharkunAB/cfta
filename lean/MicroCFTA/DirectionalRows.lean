import MicroCFTA.RelatedRows

/-!
# Exact graph languages from separate directional row simulations

A source row can be covered by a target row with larger child languages.
Guards retain an explicit implication on the full term. Separate reverse
simulation proves exact language without requiring an exact representative
for every redundant source row. Deleted rows retain explicit reasons.
-/
namespace MicroCFTA.DirectionalRows
open Language SymbolicGraphView

/-- A covering row retains its symbol, ordered related children, and the complete guard implication. -/
def Match (related : Source → Target → Prop) (source : Edge Source Symbol) (target : Edge Target Symbol) : Prop :=
  source.label = target.label ∧ (∀ term, source.guard term = true → target.guard term = true) ∧
    All₂ related source.children target.children

/-- Local source rows are covered by target rows or have a proved false guard or related empty child. -/
structure Simulation (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) : Prop where
  rows : ∀ first second, related first second → ∀ original ∈ source first,
    (∀ term, original.guard term = false) ∨
      (∃ children, All₂ related original.children children ∧ ∃ child ∈ children, target child = []) ∨
      ∃ edge ∈ target second, Match related original edge

/-- Ordered related children transport acceptance under local directional child implications. -/
theorem all₂_imp (related : Source → Target → Prop) (before : Source → Term Symbol → Prop)
    (after : Target → Term Symbol → Prop) (sources : List Source) (targets : List Target)
    (paired : All₂ related sources targets) (terms : List (Term Symbol)) (runs : All₂ before sources terms)
    (change : ∀ term ∈ terms, ∀ first second, related first second → before first term → after second term) :
    All₂ after targets terms := by
  induction paired generalizing terms with
  | nil => cases runs; exact .nil
  | cons head tail ih =>
      cases runs with
      | cons accepted rest =>
          exact .cons (change _ List.mem_cons_self _ _ head accepted)
            (ih _ rest (fun tree member first second paired => change tree (List.mem_cons_of_mem _ member) first second paired))

/-- Local directional row simulation implies full finite-term language inclusion on arbitrary cyclic graphs. -/
theorem language_included (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) (view : Simulation source target related)
    (first : Source) (second : Target) (paired : related first second) (term : Term Symbol) :
    Accepts source first term → Accepts target second term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ first second, related first second →
      Accepts source first term → Accepts target second term) generalizing first second with
  | node symbol children ih =>
      rw [accepts_node_iff, accepts_node_iff]
      rintro ⟨original, member, label, runs, guard⟩
      rcases view.rows first second paired original member with falseGuard | discarded | retained
      · have impossible := falseGuard (.node symbol children)
        rw [guard] at impossible
        cases impossible
      · obtain ⟨targets, matched, child, present, empty⟩ := discarded
        have copied := all₂_imp related (Accepts source) (Accepts target) original.children targets matched children runs
          (fun tree member left right paired accepted => ih tree member left right paired accepted)
        obtain ⟨tree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copied child present
        exact False.elim (empty_rows_reject target child empty tree accepted)
      · obtain ⟨edge, present, matched⟩ := retained
        exact ⟨edge, present, matched.1.symm.trans label,
          all₂_imp related (Accepts source) (Accepts target) original.children edge.children matched.2.2 children runs
            (fun tree member left right paired accepted => ih tree member left right paired accepted),
          matched.2.1 (.node symbol children) guard⟩
  | nil => simp_all
  | cons head tail first rest =>
      rename_i term member source target paired accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact first source target paired accepted
      · exact rest term member source target paired accepted

/-- Separate directional row proofs derive exact full language without a common child-equivalence relation. -/
theorem language_exact (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (forward : Source → Target → Prop) (reverse : Target → Source → Prop)
    (included : Simulation source target forward) (covered : Simulation target source reverse)
    (first : Source) (second : Target) (forwardRoot : forward first second) (reverseRoot : reverse second first)
    (term : Term Symbol) : Accepts target second term ↔ Accepts source first term :=
  ⟨language_included target source reverse covered second first reverseRoot term,
    language_included source target forward included first second forwardRoot term⟩

/-- Exact related rows supply the forward directional simulation with unchanged deletion reasons. -/
theorem of_related (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) (view : RelatedRows.Readback source target related) :
    Simulation source target related := by
  constructor
  intro first second paired original member
  rcases view.complete first second paired original member with falseGuard | discarded | retained
  · exact Or.inl falseGuard
  · exact Or.inr (Or.inl discarded)
  · obtain ⟨edge, present, matched⟩ := retained
    exact Or.inr (Or.inr ⟨edge, present, matched.1,
      (fun term accepted => by rw [← matched.2.1]; exact accepted), matched.2.2⟩)

/-- Reverse exact related rows also supply a directional simulation without deleted target rows. -/
theorem reverse_of_related (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) (view : RelatedRows.Readback source target related) :
    Simulation target source (fun second first => related first second) := by
  constructor
  intro second first paired edge member
  obtain ⟨original, present, matched⟩ := view.sound first second paired edge member
  refine Or.inr (Or.inr ⟨original, present, matched.1.symm, ?_, ?_⟩)
  · intro term accepted
    rw [matched.2.1]
    exact accepted
  · have children := matched.2.2
    generalize original.children = sources at children ⊢
    generalize edge.children = targets at children ⊢
    induction children with
    | nil => exact .nil
    | cons head tail ih => exact .cons head ih

end MicroCFTA.DirectionalRows
