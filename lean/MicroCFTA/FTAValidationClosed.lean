import MicroCFTA.SourceFromTermsArity

/-!
# Exact validation of closed rows with a declared initial state

Map normalization preserves declared keys and child closure. Only the
actual ordered arity scan can reject these rows. Closure alone does not
imply a ranked alphabet.
-/
namespace MicroCFTA.FTAValidation
open Language

/-- Map normalization retains child closure without an alphabet assumption. -/
theorem normalized_closed [DecidableEq State] [Ord State] (rows : Rows State Symbol) (closed : Closed rows) :
    Closed (normalizeRows rows) := by
  intro edge member child childIn
  obtain ⟨⟨state, outgoing⟩, row, found⟩ := List.mem_flatMap.mp member
  have lookup := (rowFor_exact _ _ _).mpr ⟨outgoing, row, found⟩
  rw [SourceFromTerms.normalize_lookup] at lookup
  obtain ⟨old, oldRow, oldEdge⟩ := (rowFor_exact _ _ _).mp lookup
  exact (normalized_keys rows child).mpr
    (closed edge (List.mem_flatMap.mpr ⟨(state, old), oldRow, oldEdge⟩) child childIn)

/-- Declared closed input reduces the full public builder to its actual arity scan. -/
theorem mkFTA_arity [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (initial : State) (rows : Rows State Symbol) (declared : initial ∈ rows.map Prod.fst) (closed : Closed rows) :
    mkFTA initial rows = match checkArities (fun _ => none) (arityEntries (normalizeRows rows)) with
      | .error error => .error (.inconsistent error)
      | .ok _ => .ok (normalizeRows rows) := by
  have root := (normalized_keys rows initial).mpr declared
  have children := (dangling_none (normalizeRows rows)).mpr (normalized_closed rows closed)
  simp only [mkFTA, validateRows, ite_eq_left root, children]
  rfl

/-- Successful validation of declared closed rows is equivalent to their actual ranked alphabet. -/
theorem mkFTA_ranked_iff [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (initial : State) (rows : Rows State Symbol) (declared : initial ∈ rows.map Prod.fst) (closed : Closed rows) :
    mkFTA initial rows = .ok (normalizeRows rows) ↔ ∃ assignment, Describes assignment (arityEntries rows) := by
  rw [mkFTA_exact]
  have root := (normalized_keys rows initial).mpr declared
  simp only [Valid, root, normalized_closed rows closed, true_and]
  apply exists_congr
  intro assignment
  rw [SourceFromTerms.describes_rows, SourceFromTerms.describes_rows]
  simp only [SourceFromTerms.normalize_lookup]

/-- One closed declared graph can use the same constructor at two arities. -/
def arityBoundary : Rows Unit Unit :=
  [((), [⟨(), [], fun _ => true⟩, ⟨(), [()], fun _ => true⟩])]

/-- Root membership and child closure do not remove the source arity error. -/
theorem arity_boundary : () ∈ arityBoundary.map Prod.fst ∧ Closed arityBoundary ∧
    validateRows () arityBoundary = .error (.inconsistent ⟨(), 0, 1⟩) := by
  refine ⟨by simp [arityBoundary], ?_, rfl⟩
  intro edge member child childIn
  simp only [arityBoundary, edges, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases childIn
  · simp [arityBoundary]

end MicroCFTA.FTAValidation
