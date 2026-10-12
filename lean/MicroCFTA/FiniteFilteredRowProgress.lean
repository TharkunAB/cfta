import MicroCFTA.FiniteLeafSymbolsProgress

/-!
# Structural progress when constructors reject Cartesian rows

Source constructors can remove literal Bottom or arity-invalid rows after
conjunction. The finite progress argument still applies when every row of
the input being narrowed already passes those checks. The other operand
can contain rows that will be rejected when constructed separately.
-/
namespace MicroCFTA.FiniteFilteredRowProgress
open FiniteRowIntersection

/-- Apply the actual row-admission predicate after Cartesian conjunction. -/
def product (algebra : Conjunction Row) (admitted : Row → Prop)
    (first second : Rows Row) : Rows Row :=
  fun row => FiniteRowIntersection.product algebra first second row ∧ admitted row

/-- Every admitted product row is an ordinary Cartesian row. -/
theorem upward_product (algebra : Conjunction Row) (admitted : Row → Prop)
    (first second : Rows Row) (row : Row)
    (present : upward algebra (product algebra admitted first second) row) :
    upward algebra (FiniteRowIntersection.product algebra first second) row := by
  rcases present with ⟨combined, ⟨pair, _⟩, below⟩
  exact ⟨combined, pair, below⟩

/-- Constructor rejection cannot add a member to the original upward closure. -/
theorem upward_subset (algebra : Conjunction Row) (admitted : Row → Prop)
    (first second : Rows Row) (row : Row)
    (present : upward algebra (product algebra admitted first second) row) :
    upward algebra first row :=
  product_upward_subset algebra first second row (upward_product algebra admitted first second row present)

/-- Equal closures retain every original row because that row already passes admission. -/
theorem retains (algebra : Conjunction Row) (admitted : Row → Prop) (first second : Rows Row)
    (valid : ∀ row, first row → admitted row)
    (same : ∀ row, upward algebra first row → upward algebra (product algebra admitted first second) row)
    (row : Row) (present : first row) : product algebra admitted first second row :=
  ⟨product_retains algebra first second
    (fun row member => upward_product algebra admitted first second row (same row member)) row present,
    valid row present⟩

/-- Rejected Cartesian rows preserve the strict finite structural progress measure. -/
theorem progress (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (admitted : Row → Prop) (first second : Rows Row) (valid : ∀ row, first row → admitted row)
    (changed : product algebra admitted first second ≠ first) :
    Prod.Lex (· < ·) (· < ·)
      (measure algebra inventory (product algebra admitted first second)) (measure algebra inventory first) := by
  classical
  by_cases same : upward algebra (product algebra admitted first second) = upward algebra first
  · have kept := retains algebra admitted first second valid (fun row present => same ▸ present)
    have grows := count_strict inventory complete first (product algebra admitted first second) kept (Ne.symm changed)
    have bound := count_bound inventory (product algebra admitted first second)
    have closureSame := congrArg (count inventory) same
    unfold FiniteRowIntersection.measure
    rw [closureSame]
    apply Prod.Lex.right
    omega
  · exact Prod.Lex.left _ _ (count_strict inventory complete _ _ (upward_subset algebra admitted first second) same)

/-- Each column either stays equal or decreases the scalar leaf potential. -/
theorem improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (admitted : Row → Prop) (first second : Rows Row) (valid : ∀ row, first row → admitted row) :
    FiniteLeafForestProgress.Improves algebra inventory (product algebra admitted first second) first := by
  classical
  by_cases same : product algebra admitted first second = first
  · exact Or.inl same
  · right
    have lower := progress algebra inventory complete admitted first second valid same
    have bound : (measure algebra inventory (product algebra admitted first second)).2 ≤ inventory.length := Nat.sub_le _ _
    rcases Prod.lex_def.mp lower with less | ⟨equal, less⟩
    · have multiplied := Nat.mul_le_mul_right (inventory.length + 1) (Nat.succ_le_of_lt less)
      rw [Nat.succ_mul] at multiplied
      simp only [FiniteLeafForestProgress.potential]
      omega
    · simp only [FiniteLeafForestProgress.potential]
      rw [equal]
      omega

/-- Source filtering establishes the admission invariant for every output row. -/
theorem output_admitted (algebra : Conjunction Row) (admitted : Row → Prop)
    (first second : Rows Row) (row : Row) (present : product algebra admitted first second row) : admitted row := present.2

/-- If conjunction preserves admission, filtering has no effect on already admitted operands. -/
theorem no_filter (algebra : Conjunction Row) (admitted : Row → Prop)
    (closed : ∀ left right, admitted left → admitted right → admitted (algebra.join left right))
    (first second : Rows Row) (left : ∀ row, first row → admitted row) (right : ∀ row, second row → admitted row) :
    product algebra admitted first second = FiniteRowIntersection.product algebra first second := by
  funext row
  apply propext
  constructor
  · exact And.left
  · rintro ⟨a, b, foundA, foundB, rfl⟩
    exact ⟨⟨a, b, foundA, foundB, rfl⟩, closed a b (left a foundA) (right b foundB)⟩

end MicroCFTA.FiniteFilteredRowProgress
