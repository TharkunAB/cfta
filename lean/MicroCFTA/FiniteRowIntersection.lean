import Std

/-!
# Structural progress for finite alternative rows

Cartesian conjunction can add rows, even when each row conjunction is
idempotent. Count the upward closure first. If that closure does not change,
Cartesian conjunction retains every old row. This gives a strict finite
measure without assuming absorption of whole alternative sets.
-/
namespace MicroCFTA.FiniteRowIntersection

/-- The conjunction laws hold for individual canonical rows. -/
structure Conjunction (Row : Type) where
  join : Row → Row → Row
  assoc : ∀ a b c, join (join a b) c = join a (join b c)
  comm : ∀ a b, join a b = join b a
  idem : ∀ a, join a a = a

/-- A row includes all conjuncts of another row. -/
def Below (algebra : Conjunction Row) (first second : Row) : Prop :=
  algebra.join first second = second

/-- Alternative rows have set membership. Canonical source storage removes duplicates. -/
abbrev Rows (Row : Type) := Row → Prop

/-- Cartesian intersection retains every pairwise row conjunction. -/
def product (algebra : Conjunction Row) (first second : Rows Row) : Rows Row :=
  fun row => ∃ left right, first left ∧ second right ∧ algebra.join left right = row

/-- Upward closure records all rows which contain an existing alternative. -/
def upward (algebra : Conjunction Row) (rows : Rows Row) : Rows Row :=
  fun row => ∃ original, rows original ∧ Below algebra original row

/-- Each individual row is below itself. -/
theorem below_refl (algebra : Conjunction Row) (row : Row) : Below algebra row row := algebra.idem row

/-- Row inclusion is transitive under associative conjunction. -/
theorem below_trans (algebra : Conjunction Row) {first middle last : Row}
    (before : Below algebra first middle) (after : Below algebra middle last) : Below algebra first last := by
  unfold Below at *
  rw [← after, ← algebra.assoc, before]

/-- Each factor contributes all of its conjuncts to the product. -/
theorem below_join_left (algebra : Conjunction Row) (first second : Row) :
    Below algebra first (algebra.join first second) := by
  unfold Below
  rw [← algebra.assoc, algebra.idem]

/-- The second factor also contributes all of its conjuncts. -/
theorem below_join_right (algebra : Conjunction Row) (first second : Row) :
    Below algebra second (algebra.join first second) := by
  rw [algebra.comm first second]
  exact below_join_left algebra second first

/-- Every row belongs to its upward closure. -/
theorem upward_self (algebra : Conjunction Row) (rows : Rows Row) (row : Row) (present : rows row) :
    upward algebra rows row := ⟨row, present, below_refl algebra row⟩

/-- Cartesian intersection can only remove members of the upward closure. -/
theorem product_upward_subset (algebra : Conjunction Row) (first second : Rows Row) (row : Row)
    (present : upward algebra (product algebra first second) row) : upward algebra first row := by
  obtain ⟨combined, ⟨left, right, firstPresent, _, same⟩, above⟩ := present
  subst combined
  exact ⟨left, firstPresent, below_trans algebra (below_join_left algebra left right) above⟩

/-- An unchanged upward closure forces every old row to remain in the product.
This conclusion does not assert that the product adds no rows. -/
theorem product_retains (algebra : Conjunction Row) (first second : Rows Row)
    (same : ∀ row, upward algebra first row → upward algebra (product algebra first second) row)
    (row : Row) (present : first row) : product algebra first second row := by
  obtain ⟨combined, ⟨left, right, _, rightPresent, combinedEq⟩, above⟩ :=
    same row (upward_self algebra first row present)
  subst combined
  have rightBelow := below_trans algebra (below_join_right algebra left right) above
  exact ⟨row, right, present, rightPresent, (algebra.comm row right).trans rightBelow⟩

/-- Count selected rows in a fixed finite inventory. -/
noncomputable def count (inventory : List Row) (rows : Rows Row) : Nat := by
  classical
  exact inventory.countP (fun row => decide (rows row))

/-- Removing rows cannot increase their finite count. -/
theorem count_mono (inventory : List Row) (first second : Rows Row)
    (included : ∀ row ∈ inventory, first row → second row) : count inventory first ≤ count inventory second := by
  classical
  apply List.countP_mono_left
  simpa using included

/-- Counts are bounded by the number of slots in the finite inventory. -/
theorem count_bound (inventory : List Row) (rows : Rows Row) : count inventory rows ≤ inventory.length := by
  classical
  exact List.countP_le_length

/-- Included finite row sets with equal counts agree on every inventory member. -/
theorem count_equal (inventory : List Row) (first second : Rows Row)
    (included : ∀ row ∈ inventory, first row → second row)
    (same : count inventory first = count inventory second) :
    ∀ row ∈ inventory, first row ↔ second row := by
  classical
  induction inventory with
  | nil => simp
  | cons head rest ih =>
      have tailIncluded : ∀ row ∈ rest, first row → second row := fun row member => included row (by simp [member])
      have tailBound := count_mono rest first second tailIncluded
      have headIncluded := included head (by simp)
      have headSame : first head ↔ second head := by
        by_cases a : first head <;> by_cases b : second head
        all_goals simp_all [count]
        omega
      have tailSame : count rest first = count rest second := by
        simpa [count, List.countP_cons, headSame] using same
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact headSame
      · exact ih tailIncluded tailSame row member

/-- Strict set inclusion strictly increases the finite count. -/
theorem count_strict (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (first second : Rows Row) (included : ∀ row, first row → second row) (different : first ≠ second) :
    count inventory first < count inventory second := by
  have bound := count_mono inventory first second (fun row _ => included row)
  apply Nat.lt_of_le_of_ne bound
  intro same
  apply different
  funext row
  exact propext (count_equal inventory first second (fun row _ => included row) same row (complete row))

/-- First decrease the closure count. Then decrease the number of missing rows. -/
noncomputable def measure (algebra : Conjunction Row) (inventory : List Row) (rows : Rows Row) : Nat × Nat :=
  (count inventory (upward algebra rows), inventory.length - count inventory rows)

/-- Every changing Cartesian narrowing step strictly decreases a finite structural measure. -/
theorem product_progress (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (first second : Rows Row) (changed : product algebra first second ≠ first) :
    Prod.Lex (· < ·) (· < ·) (measure algebra inventory (product algebra first second)) (measure algebra inventory first) := by
  classical
  by_cases same : upward algebra (product algebra first second) = upward algebra first
  · have retained := product_retains algebra first second (fun row present => same ▸ present)
    have grows := count_strict inventory complete first (product algebra first second) retained (Ne.symm changed)
    have bound := count_bound inventory (product algebra first second)
    have closureSame : count inventory (upward algebra (product algebra first second)) =
        count inventory (upward algebra first) := congrArg (count inventory) same
    unfold measure
    rw [closureSame]
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    exact count_strict inventory complete _ _ (product_upward_subset algebra first second) same

/-- The source self-intersection shortcut preserves the state exactly. -/
noncomputable def intersect (algebra : Conjunction Row) (first second : Rows Row) : Rows Row := by
  classical
  exact if first = second then first else product algebra first second

/-- The exact self shortcut cannot invalidate the structural progress measure. -/
theorem intersect_progress (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (first second : Rows Row) (changed : intersect algebra first second ≠ first) :
    Prod.Lex (· < ·) (· < ·) (measure algebra inventory (intersect algebra first second)) (measure algebra inventory first) := by
  classical
  unfold intersect at changed ⊢
  by_cases same : first = second
  · simp [same] at changed
  · simp only [same, ↓reduceIte] at changed ⊢
    exact product_progress algebra inventory complete first second changed

/-- Follow the source fixed-point schedule with an explicit diagnostic bound. -/
noncomputable def run (algebra : Conjunction Row) (choose : Rows Row → Rows Row) :
    Nat → Rows Row → Option (Rows Row)
  | 0, _ => none
  | fuel + 1, rows => by
      classical
      exact let next := intersect algebra rows (choose rows)
        if next = rows then some rows else run algebra choose fuel next

/-- Every deterministic choice of narrowing operands reaches an identity fixed point.
The operand may change after every pass. -/
theorem run_terminates (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (choose : Rows Row → Rows Row) (rows : Rows Row) :
    ∃ fuel result, run algebra choose fuel rows = some result ∧ intersect algebra result (choose result) = result := by
  classical
  let next := intersect algebra rows (choose rows)
  by_cases same : next = rows
  · exact ⟨1, rows, by simp [run, next] at same ⊢; exact same, same⟩
  · obtain ⟨fuel, result, finished, fixed⟩ := run_terminates algebra inventory complete choose next
    exact ⟨fuel + 1, result, by simpa only [run, show intersect algebra rows (choose rows) = next from rfl,
      same, ↓reduceIte] using finished, fixed⟩
termination_by measure algebra inventory rows
decreasing_by exact intersect_progress algebra inventory complete rows (choose rows) same

end MicroCFTA.FiniteRowIntersection
