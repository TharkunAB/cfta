import MicroCFTA.SourceCyclicRowsNativeGateRelational

/-!
# The retained Mu row-identity witness as finite explicit graphs

The live row transcript has source identities 7, 11, and 12. Its additional
product identities are 18, 19, and 21. Each state has an `a` leaf row and an
`f` unary row. This module proves the full graph-language result and the
literal functional-row obstruction. It does not verify Haskell extraction.
-/
namespace MicroCFTA.NativeProductRowCycleReadout
open Language SymbolicGraphView

/-- Read an `a` leaf row and an `f` row with the selected successor. -/
def rows (next : State → State) : Automaton State Nat :=
  fun state => [⟨0, [], fun _ => true⟩, ⟨1, [next state], fun _ => true⟩]

/-- These complete unary rows have the same two synchronous rows after diagonal reuse. -/
theorem product_rows [DecidableEq State] (next : State → State) (first second : State) :
    DiagonalProduct.graph (rows next) (first, second) =
      [⟨0, [], fun _ => true⟩, ⟨1, [(next first, next second)], fun _ => true⟩] := by
  by_cases same : first = second
  · subst second
    simp [DiagonalProduct.graph, rows, renameEdge]
  · simp [DiagonalProduct.graph, same, rows, Language.intersect, Language.intersectEdge]

/-- Complete unary rows have an explicit related-row proof for every pair and physical representative. -/
theorem readback [DecidableEq Source] (sourceNext : Source → Source) (targetNext : Target → Target) :
    RelatedRows.Readback (DiagonalProduct.graph (rows sourceNext)) (rows targetNext) (fun _ _ => True) := by
  constructor
  · rintro ⟨first, second⟩ result paired edge member
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨0, [], fun _ => true⟩, by rw [product_rows]; exact List.mem_cons_self, rfl, rfl, .nil⟩
    · exact ⟨⟨1, [(sourceNext first, sourceNext second)], fun _ => true⟩,
        by rw [product_rows]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, .cons trivial .nil⟩
  · rintro ⟨first, second⟩ result paired original member
    rw [product_rows] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr (Or.inr ⟨⟨0, [], fun _ => true⟩, List.mem_cons_self, rfl, rfl, .nil⟩)
    · exact Or.inr (Or.inr ⟨⟨1, [targetNext result], fun _ => true⟩, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, .cons trivial .nil⟩)

/-- Source indices 0, 1, and 2 name live identities 7, 11, and 12. -/
def sourceNext (state : Fin 3) : Fin 3 := if state = 2 then 1 else 2

/-- Product indices 0, 1, and 2 name live identities 18, 19, and 21. -/
def copyNext (state : Fin 3) : Fin 3 := if state = 2 then 1 else 0

/-- Retain all original source states and the additional product states in one explicit target graph. -/
def targetNext : Sum (Fin 3) (Fin 3) → Sum (Fin 3) (Fin 3)
  | .inl state => .inl (sourceNext state)
  | .inr state => .inr (copyNext state)

/-- The observed source graph retains complete guards and both symbol arities. -/
def source : Automaton (Fin 3) Nat := rows sourceNext

/-- The observed target graph also retains original source records. -/
def target : Automaton (Sum (Fin 3) (Fin 3)) Nat := rows targetNext

/-- Original source records have exact copied rows in the target graph. -/
theorem copied_rows : RowsCorrespond source target Sum.inl := by
  intro state edge
  have same : target (.inl state) = (source state).map (renameEdge Sum.inl) := by
    simp [target, source, rows, targetNext, renameEdge]
  rw [same]
  constructor
  · intro member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨original, present, rfl⟩
  · rintro ⟨original, present, rfl⟩
    exact List.mem_map.mpr ⟨original, present, rfl⟩

/-- Every physical representative in this transcript has the exact complete common input language. -/
theorem full_product_language (first second : Fin 3) (result : Sum (Fin 3) (Fin 3)) (term : Term Nat) :
    Accepts target result term ↔ Accepts source first term ∧ Accepts source second term :=
  DiagonalProduct.related_product_exact source target (fun _ _ => True) (readback sourceNext targetNext) first second result trivial term

/-- The actual product root and separately rebuilt parent have equal full languages. -/
theorem representatives_equal (term : Term Nat) :
    Accepts target (.inr 1) term ↔ Accepts target (.inr 2) term :=
  (full_product_language 0 2 (.inr 1) term).trans (full_product_language 0 2 (.inr 2) term).symm

/-- Their complete row lists have distinct physical child identities. -/
theorem literal_rows_differ : target (.inr 1) ≠ target (.inr 2) := by
  intro same
  have distinct : (target (.inr 1)).map Edge.children ≠ (target (.inr 2)).map Edge.children := by decide
  exact distinct (congrArg (fun edges => edges.map Edge.children) same)

/-- The observed parent and child results exclude the general functional row contract, even with exact original row copying. -/
theorem no_functional_readback (meet : Fin 3 → Fin 3 → Sum (Fin 3) (Fin 3))
    (root : meet 0 2 = .inr 1) (child : meet 2 1 = .inr 1) :
    ¬ Nonempty (SourceCyclicRowsNativeGate.ProductReadback source target Sum.inl meet) := by
  rintro ⟨view⟩
  have member : (⟨1, [.inr 0], fun _ => true⟩ : Edge (Sum (Fin 3) (Fin 3)) Nat) ∈ target (meet 0 2) := by
    rw [root]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨original, present, _, equal⟩ := (view.members 0 2 (by decide) _).mp member
  have exactRows : Language.intersect source source (0, 2) =
      [⟨0, [], fun _ => true⟩, ⟨1, [(2, 1)], fun _ => true⟩] := by
    simp [Language.intersect, Language.intersectEdge, source, rows, sourceNext]
  rw [exactRows] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · have bad := congrArg Edge.label equal
    cases bad
  · have bad := congrArg Edge.children equal
    simp only [renameEdge, List.map_cons, List.map_nil, child, List.cons.injEq, and_true] at bad
    have impossible : (Sum.inr (0 : Fin 3) : Sum (Fin 3) (Fin 3)) ≠ .inr 1 := by decide
    exact impossible bad

end MicroCFTA.NativeProductRowCycleReadout
