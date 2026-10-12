import MicroCFTA.FiniteFilteredRowProgress

/-!
# Initial noncanonical rows and the source whole-node shortcut

An unchanged self-intersection keeps the original rows. Every Cartesian
product canonicalizes its rows and applies constructor admission. Once a
node is canonical, filtered row progress supplies the remaining decrease.
-/
namespace MicroCFTA.NoncanonicalLeafProgress
open FiniteRowIntersection

/-- The canonical image retains rows even when separate constructor admission would reject them. -/
def image (normalize : Raw → Row) (rows : Rows Raw) : Rows Row :=
  fun row => ∃ raw, rows raw ∧ normalize raw = row

/-- Embed accepted canonical rows into the original source row representation. -/
def embedRows (embed : Row → Raw) (rows : Rows Row) : Rows Raw :=
  fun raw => ∃ row, rows row ∧ embed row = raw

/-- Normalizing an embedded canonical row leaves it unchanged. -/
theorem image_embed (normalize : Raw → Row) (embed : Row → Raw) (retraction : ∀ row, normalize (embed row) = row)
    (rows : Rows Row) : image normalize (embedRows embed rows) = rows := by
  funext row
  apply propext
  constructor
  · rintro ⟨raw, ⟨original, present, rfl⟩, same⟩
    rw [retraction] at same
    exact same ▸ present
  · intro present
    exact ⟨embed row, ⟨row, present, rfl⟩, retraction row⟩

/-- Node alternatives retain their separate constructor symbols. -/
abbrev Node (Raw : Type) (symbols : Nat) := Fin symbols → Rows Raw

/-- Every stored row is canonical and passes the actual constructor predicate. -/
def Ready (normalize : Raw → Row) (embed : Row → Raw) (admitted : Row → Prop) (node : Node Raw symbols) : Prop :=
  ∀ symbol raw, node symbol raw → embed (normalize raw) = raw ∧ admitted (normalize raw)

/-- Canonical input image rows inherit the source admission check. -/
theorem image_admitted (normalize : Raw → Row) (embed : Row → Raw) (admitted : Row → Prop)
    (node : Node Raw symbols) (ready : Ready normalize embed admitted node) (symbol : Fin symbols) (row : Row)
    (present : image normalize (node symbol) row) : admitted row := by
  rcases present with ⟨raw, present, rfl⟩
  exact (ready symbol raw present).2

/-- Exact canonical images distinguish ready source nodes. -/
theorem ready_injective (normalize : Raw → Row) (embed : Row → Raw) (admitted : Row → Prop)
    (first second : Node Raw symbols) (firstReady : Ready normalize embed admitted first)
    (secondReady : Ready normalize embed admitted second)
    (same : ∀ symbol, image normalize (first symbol) = image normalize (second symbol)) : first = second := by
  funext symbol raw
  apply propext
  constructor
  · intro present
    have normalized : image normalize (second symbol) (normalize raw) := by
      rw [← same symbol]
      exact ⟨raw, present, rfl⟩
    rcases normalized with ⟨other, found, equal⟩
    have identical : other = raw := (secondReady symbol other found).1.symm.trans
      ((congrArg embed equal).trans (firstReady symbol raw present).1)
    simpa only [identical] using found
  · intro present
    have normalized : image normalize (first symbol) (normalize raw) := by
      rw [same symbol]
      exact ⟨raw, present, rfl⟩
    rcases normalized with ⟨other, found, equal⟩
    have identical : other = raw := (firstReady symbol other found).1.symm.trans
      ((congrArg embed equal).trans (secondReady symbol raw present).1)
    simpa only [identical] using found

/-- Each Cartesian source branch normalizes row factors and then checks the completed row. -/
def product (algebra : Conjunction Row) (normalize : Raw → Row) (embed : Row → Raw)
    (admitted : Row → Prop) (first second : Node Raw symbols) : Node Raw symbols := fun symbol =>
  embedRows embed (FiniteFilteredRowProgress.product algebra admitted
    (image normalize (first symbol)) (image normalize (second symbol)))

/-- Every actual Cartesian result establishes the canonical source row invariant. -/
theorem product_ready (algebra : Conjunction Row) (normalize : Raw → Row) (embed : Row → Raw)
    (retraction : ∀ row, normalize (embed row) = row) (admitted : Row → Prop) (first second : Node Raw symbols) :
    Ready normalize embed admitted (product algebra normalize embed admitted first second) := by
  rintro symbol raw ⟨row, present, rfl⟩
  simpa only [retraction] using And.intro (Eq.refl (embed row)) present.2

/-- Source self-intersection keeps the entire original node, including unnormalized guards. -/
noncomputable def intersect (algebra : Conjunction Row) (normalize : Raw → Row) (embed : Row → Raw)
    (admitted : Row → Prop) (first second : Node Raw symbols) : Node Raw symbols := by
  classical
  exact if first = second then first else product algebra normalize embed admitted first second

/-- Sum the finite canonical potentials without discarding normalization images. -/
noncomputable def potential (algebra : Conjunction Row) (inventory : List Row) (normalize : Raw → Row)
    (node : Node Raw symbols) : Nat :=
  ((List.ofFn id : List (Fin symbols)).map fun symbol =>
    FiniteLeafForestProgress.potential algebra inventory (image normalize (node symbol))).sum

/-- One canonical row potential is bounded solely by the generated finite inventory. -/
theorem row_bound (algebra : Conjunction Row) (inventory : List Row) (rows : Rows Row) :
    FiniteLeafForestProgress.potential algebra inventory rows ≤ inventory.length * (inventory.length + 1) + inventory.length := by
  have closures := count_bound inventory (upward algebra rows)
  have multiplied := Nat.mul_le_mul_right (inventory.length + 1) closures
  have missing : inventory.length - count inventory rows ≤ inventory.length := Nat.sub_le _ _
  simp only [FiniteLeafForestProgress.potential, FiniteRowIntersection.measure]
  omega

/-- The finite symbol inventory bounds every canonical node potential. -/
theorem potential_bound (algebra : Conjunction Row) (inventory : List Row) (normalize : Raw → Row) (node : Node Raw symbols) :
    potential algebra inventory normalize node ≤ symbols * (inventory.length * (inventory.length + 1) + inventory.length) := by
  have bound : ∀ positions : List (Fin symbols),
      (positions.map fun symbol => FiniteLeafForestProgress.potential algebra inventory (image normalize (node symbol))).sum ≤
        positions.length * (inventory.length * (inventory.length + 1) + inventory.length) := by
    intro positions
    induction positions with
    | nil => simp
    | cons symbol rest ih =>
        have head := row_bound algebra inventory (image normalize (node symbol))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  simpa only [potential, List.length_ofFn] using bound (List.ofFn id)

/-- Canonical input nodes strictly improve under every changing Cartesian constructor result. -/
theorem product_strict (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (normalize : Raw → Row) (embed : Row → Raw) (retraction : ∀ row, normalize (embed row) = row)
    (admitted : Row → Prop) (first second : Node Raw symbols) (ready : Ready normalize embed admitted first)
    (changed : product algebra normalize embed admitted first second ≠ first) :
    potential algebra inventory normalize (product algebra normalize embed admitted first second) <
      potential algebra inventory normalize first := by
  have columns := FiniteLeafForestProgress.sum_progress algebra inventory (List.ofFn id : List (Fin symbols))
    (fun symbol => image normalize (first symbol))
    (fun symbol => image normalize (product algebra normalize embed admitted first second symbol))
    (fun symbol _ => by
      rw [product, image_embed normalize embed retraction]
      exact FiniteFilteredRowProgress.improves algebra inventory complete admitted _ _
        (fun row present => image_admitted normalize embed admitted first ready symbol row present))
  apply Nat.lt_of_le_of_ne columns.1
  intro equal
  apply changed
  exact ready_injective normalize embed admitted _ first
    (product_ready algebra normalize embed retraction admitted first second) ready
    (fun symbol => columns.2 equal symbol (by simp))

/-- One extra phase level accounts for every raw initial node. -/
noncomputable def rank (algebra : Conjunction Row) (inventory : List Row) (normalize : Raw → Row)
    (embed : Row → Raw) (admitted : Row → Prop) (node : Node Raw symbols) : Nat := by
  classical
  exact if Ready normalize embed admitted node then potential algebra inventory normalize node
    else symbols * (inventory.length * (inventory.length + 1) + inventory.length) + 1

/-- The exact whole-node shortcut plus canonicalizing Cartesian branch has strict finite progress. -/
theorem intersect_strict (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (normalize : Raw → Row) (embed : Row → Raw) (retraction : ∀ row, normalize (embed row) = row)
    (admitted : Row → Prop) (first second : Node Raw symbols)
    (changed : intersect algebra normalize embed admitted first second ≠ first) :
    rank algebra inventory normalize embed admitted (intersect algebra normalize embed admitted first second) <
      rank algebra inventory normalize embed admitted first := by
  classical
  have different : first ≠ second := by intro same; subst second; simp [intersect] at changed
  simp only [intersect, different, ↓reduceIte] at changed ⊢
  have afterReady := product_ready algebra normalize embed retraction admitted first second
  by_cases ready : Ready normalize embed admitted first
  · simpa only [rank, ite_eq_left ready, ite_eq_left afterReady] using
      product_strict algebra inventory complete normalize embed retraction admitted first second ready changed
  · simp only [rank, ite_eq_right ready, ite_eq_left afterReady]
    exact Nat.lt_succ_of_le (potential_bound algebra inventory normalize _)

end MicroCFTA.NoncanonicalLeafProgress
