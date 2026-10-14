import MicroCFTA.SymbolicNormalizedRows

/-!
# Exact graph languages from related physical rows

A source state can have several physical representatives. Matching rows
retain complete guards and ordered related children. Deleted rows have a
false guard or a chosen related child with no outgoing rows. Every edge
consumes one constructor, so finite-term induction proves exact languages.
-/
namespace MicroCFTA.RelatedRows
open Language SymbolicGraphView

/-- A physical row retains its source symbol, complete guard, and ordered related children. -/
def Match (related : Source → Target → Prop) (source : Edge Source Symbol) (target : Edge Target Symbol) : Prop :=
  source.label = target.label ∧ source.guard = target.guard ∧ All₂ related source.children target.children

/-- Local physical row correspondence permits several representatives and justified deleted rows. -/
structure Readback (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) : Prop where
  sound : ∀ first second, related first second → ∀ edge ∈ target second,
    ∃ original ∈ source first, Match related original edge
  complete : ∀ first second, related first second → ∀ original ∈ source first,
    (∀ term, original.guard term = false) ∨
      (∃ children, All₂ related original.children children ∧ ∃ child ∈ children, target child = []) ∨
      ∃ edge ∈ target second, Match related original edge

/-- Related ordered children preserve forest acceptance when each child term has the required local equivalence. -/
theorem all₂_exact (related : Source → Target → Prop) (before : Source → Term Symbol → Prop)
    (after : Target → Term Symbol → Prop) (sources : List Source) (targets : List Target)
    (paired : All₂ related sources targets) (terms : List (Term Symbol))
    (change : ∀ term ∈ terms, ∀ first second, related first second → (before first term ↔ after second term)) :
    All₂ before sources terms ↔ All₂ after targets terms := by
  induction paired generalizing terms with
  | nil =>
      cases terms <;> constructor <;> intro accepted <;> cases accepted
      all_goals exact .nil
  | @cons first second sources targets head tail ih =>
      cases terms with
      | nil => constructor <;> intro accepted <;> cases accepted
      | cons term terms =>
          have same := change term List.mem_cons_self first second head
          have rest := ih terms (fun tree member left right pair => change tree (List.mem_cons_of_mem _ member) left right pair)
          constructor
          · intro accepted
            cases accepted with
            | cons own later => exact .cons (same.mp own) (rest.mp later)
          · intro accepted
            cases accepted with
            | cons own later => exact .cons (same.mpr own) (rest.mpr later)

/-- Local related rows and explicit deletion reasons give exact least finite-run graph languages. -/
theorem language_exact (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (related : Source → Target → Prop) (view : Readback source target related)
    (first : Source) (second : Target) (paired : related first second) (term : Term Symbol) :
    Accepts target second term ↔ Accepts source first term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ first second, related first second →
      (Accepts target second term ↔ Accepts source first term)) generalizing first second with
  | node symbol children ih =>
      rw [accepts_node_iff, accepts_node_iff]
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        obtain ⟨original, present, matched⟩ := view.sound first second paired edge member
        have forests := all₂_exact related (Accepts source) (Accepts target) original.children edge.children matched.2.2 children
          (fun tree member left right pair => (ih tree member left right pair).symm)
        exact ⟨original, present, matched.1.trans label, forests.mpr runs, by rw [matched.2.1]; exact guard⟩
      · rintro ⟨original, member, label, runs, guard⟩
        rcases view.complete first second paired original member with falseGuard | discarded | retained
        · have impossible := falseGuard (.node symbol children)
          rw [guard] at impossible
          cases impossible
        · obtain ⟨targets, matched, child, present, empty⟩ := discarded
          have copied := (all₂_exact related (Accepts source) (Accepts target) original.children targets matched children
            (fun tree member left right pair => (ih tree member left right pair).symm)).mp runs
          obtain ⟨tree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copied child present
          exact False.elim (SymbolicGraphView.empty_rows_reject target child empty tree accepted)
        · obtain ⟨edge, present, matched⟩ := retained
          have forests := all₂_exact related (Accepts source) (Accepts target) original.children edge.children matched.2.2 children
            (fun tree member left right pair => (ih tree member left right pair).symm)
          exact ⟨edge, present, matched.1.symm.trans label, forests.mp runs, by rw [← matched.2.1]; exact guard⟩
  | nil => simp_all
  | cons head tail first rest =>
      rename_i term member source target paired
      rcases List.mem_cons.mp member with rfl | member
      · exact first source target paired
      · exact rest term member source target paired

/-- A literal renamed row is a related row for the graph of its child map. -/
theorem rename_match (encode : Source → Target) (edge : Edge Source Symbol) :
    Match (fun first second => second = encode first) edge (renameEdge encode edge) := by
  refine ⟨rfl, rfl, ?_⟩
  change All₂ (fun first second => second = encode first) edge.children (edge.children.map encode)
  induction edge.children with
  | nil => exact .nil
  | cons first rest ih => exact .cons rfl ih

/-- The existing functional normalized-row contract supplies the more general related-row interface. -/
theorem of_normalized (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (view : NormalizedRows source target encode) :
    Readback source target (fun first second => second = encode first) := by
  constructor
  · rintro first second rfl edge member
    obtain ⟨original, present, _, rfl⟩ := (view.members first edge).mp member
    exact ⟨original, present, rename_match encode original⟩
  · rintro first second rfl original member
    cases kept : view.keep first original with
    | true =>
        exact Or.inr (Or.inr ⟨renameEdge encode original,
          (view.members first _).mpr ⟨original, member, kept, rfl⟩, rename_match encode original⟩)
    | false =>
        rcases view.rejected first original member kept with falseGuard | ⟨child, present, empty⟩
        · exact Or.inl falseGuard
        · exact Or.inr (Or.inl ⟨original.children.map encode, (rename_match encode original).2.2,
            encode child, List.mem_map.mpr ⟨child, present, rfl⟩, empty⟩)

end MicroCFTA.RelatedRows
