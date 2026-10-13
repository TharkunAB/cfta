import MicroCFTA.SourceFromTerms

/-!
# Exact arity validation for finite-term reconstruction

The builder cannot fail its initial-state or closedness checks. It succeeds
exactly when every occurrence of one symbol has the same child count.
An arity failure remains an error; it does not denote an empty language.
-/
namespace MicroCFTA.SourceFromTerms
open Language FTAValidation

variable [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))]

/-- One symbol has one arity throughout every input term. -/
def Ranked (input : List (Term Symbol)) (assignment : Symbol → Nat) : Prop :=
  ∀ symbol children, Term.node symbol children ∈ input.flatMap FromTerms.subterms →
    assignment symbol = children.length

omit [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))] in
/-- Arity declarations and row lookups expose the same constructors. -/
theorem describes_rows [DecidableEq State] (table : Rows State Symbol) (assignment : Symbol → Nat) :
    Describes assignment (arityEntries table) ↔
      ∀ state edge, edge ∈ rowFor table state → assignment edge.label = edge.children.length := by
  constructor
  · intro described state edge member
    obtain ⟨outgoing, row, found⟩ := (rowFor_exact _ _ _).mp member
    exact described (edge.label, edge.children.length)
      (List.mem_map.mpr ⟨edge, List.mem_flatMap.mpr ⟨(state, outgoing), row, found⟩, rfl⟩)
  · intro described entry member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    obtain ⟨⟨state, outgoing⟩, row, found⟩ := List.mem_flatMap.mp edgeIn
    exact described state edge ((rowFor_exact _ _ _).mpr ⟨outgoing, row, found⟩)

/-- Sorted map validation checks exactly the original input constructor arities. -/
theorem ranked_entries (input : List (Term Symbol)) (assignment : Symbol → Nat) :
    Describes assignment (arityEntries (normalizeRows (rows input))) ↔ Ranked input assignment := by
  rw [describes_rows]
  simp only [normalize_lookup]
  constructor
  · intro described symbol children present
    have member : FromTerms.transition (.node symbol children) ∈ graph input (some (.node symbol children)) := by
      simp [graph_some, present]
    simpa [FromTerms.transition] using described (some (.node symbol children))
      (FromTerms.transition (.node symbol children)) member
  · intro ranked state edge member
    obtain ⟨term, nested, same⟩ := FromTerms.row_origin input state edge ((graph_members input state edge).mp member)
    subst edge
    cases term with
    | node symbol children => simpa [FromTerms.transition] using ranked symbol children nested

/-- Normalized rows still contain every child state. -/
theorem normalized_closed (input : List (Term Symbol)) : Closed (normalizeRows (rows input)) := by
  intro edge member child childIn
  obtain ⟨⟨state, outgoing⟩, row, found⟩ := List.mem_flatMap.mp member
  have lookup := (rowFor_exact _ _ _).mpr ⟨outgoing, row, found⟩
  rw [normalize_lookup] at lookup
  obtain ⟨old, oldRow, oldEdge⟩ := (rowFor_exact _ _ _).mp lookup
  exact (normalized_keys _ child).mpr
    (rows_closed input edge (List.mem_flatMap.mpr ⟨(state, old), oldRow, oldEdge⟩) child childIn)

/-- Only the arity scan can reject source-generated finite rows. -/
theorem build_equation (input : List (Term Symbol)) :
    build input = match checkArities (fun _ => none) (arityEntries (normalizeRows (rows input))) with
      | .error error => .error (.inconsistent error)
      | .ok _ => .ok (normalizeRows (rows input)) := by
  have initial := (normalized_keys (rows input) none).mpr (initial_present input)
  have closed := (dangling_none (normalizeRows (rows input))).mpr (normalized_closed input)
  simp [build, mkFTA, validateRows, initial, closed]
  rfl

/-- The exact successful public result is equivalent to ranked input terms. -/
theorem build_ok_iff (input : List (Term Symbol)) :
    build input = .ok (normalizeRows (rows input)) ↔ ∃ assignment, Ranked input assignment := by
  rw [build, mkFTA_exact]
  have initial := (normalized_keys (rows input) none).mpr (initial_present input)
  simp only [Valid, initial, normalized_closed, true_and, ranked_entries]

/-- Finite reconstruction succeeds exactly on a consistent ranked alphabet. -/
theorem build_succeeds (input : List (Term Symbol)) :
    (∃ result, build input = .ok result) ↔ ∃ assignment, Ranked input assignment := by
  constructor
  · rintro ⟨result, success⟩
    have same := mkFTA_returns none (rows input) result success
    subst result
    exact (build_ok_iff input).mp success
  · intro ranked
    exact ⟨_, (build_ok_iff input).mpr ranked⟩

/-- The empty language builds successfully with an empty root row. -/
theorem build_empty : build ([] : List (Term Symbol)) = .ok (normalizeRows (rows [])) := by
  apply (build_ok_iff []).mpr
  exact ⟨fun _ => 0, by simp [Ranked]⟩

/-- Two different child counts at one symbol force validation failure. -/
theorem inconsistent_rejected (input : List (Term Symbol)) (symbol : Symbol)
    (first second : List (Term Symbol))
    (firstIn : Term.node symbol first ∈ input.flatMap FromTerms.subterms)
    (secondIn : Term.node symbol second ∈ input.flatMap FromTerms.subterms)
    (different : first.length ≠ second.length) :
    ¬∃ result, build input = .ok result := by
  intro success
  obtain ⟨assignment, ranked⟩ := (build_succeeds input).mp success
  exact different ((ranked symbol first firstIn).symm.trans (ranked symbol second secondIn))

end MicroCFTA.SourceFromTerms
