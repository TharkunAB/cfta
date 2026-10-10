import MicroCFTA.Lattice

/-!
# Exact sums with finite support

`HasSum` describes a sum over all values of a discrete type. Its finite witness
must contain every nonzero value and must not contain duplicate values. The
sum is independent of the witness. Integer intervals supply concrete witnesses
for the polynomial eliminator.
-/

namespace MicroCFTA.FiniteSum

local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

/-- Sum a function over an explicit finite list. -/
def listSum : List α → (α → Rat) → Rat
  | [], _ => 0
  | item :: rest, value => value item + listSum rest value

theorem listSum_eq (items : List α) (value : α → Rat) : listSum items value = (items.map value).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [listSum, List.map_cons, List.sum_cons, ih]

theorem listSum_congr (items : List α) (left right : α → Rat)
    (same : ∀ item ∈ items, left item = right item) : listSum items left = listSum items right := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [listSum, listSum, same item (by simp), ih (fun entry member => same entry (by simp [member]))]

@[simp] theorem listSum_zero (items : List α) : listSum items (fun _ => 0) = 0 := by
  induction items with
  | nil => rfl
  | cons item rest ih => rw [listSum, ih, Rat.zero_add]

theorem listSum_append (left right : List α) (value : α → Rat) :
    listSum (left ++ right) value = listSum left value + listSum right value := by
  induction left with
  | nil => simp [listSum, Rat.zero_add]
  | cons item rest ih => simp [listSum, ih, Rat.add_assoc]

theorem listSum_add (items : List α) (left right : α → Rat) :
    listSum items (fun item => left item + right item) = listSum items left + listSum items right := by
  induction items with
  | nil => simp [listSum, Rat.add_zero]
  | cons item rest ih => simp only [listSum, ih]; ac_rfl

theorem listSum_map (items : List α) (map : α → β) (value : β → Rat) :
    listSum (items.map map) value = listSum items (fun item => value (map item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [listSum, ih]

/-- Exchange two finite summation orders. -/
theorem listSum_exchange (left : List α) (right : List β) (value : α → β → Rat) :
    listSum left (fun a => listSum right (value a)) =
      listSum right (fun b => listSum left (fun a => value a b)) := by
  induction left with
  | nil => simp [listSum]
  | cons item rest ih =>
    simp only [listSum, listSum_add, ih]

/-- A duplicate-free list counts a selected value at most once. -/
theorem listSum_single [DecidableEq α] (items : List α) (unique : items.Nodup) (selected : α) (value : Rat) :
    listSum items (fun item => if item = selected then value else 0) = if selected ∈ items then value else 0 := by
  induction items with
  | nil => simp [listSum]
  | cons item rest ih =>
    have facts := List.nodup_cons.mp unique
    by_cases same : item = selected
    · subst item
      simp only [listSum, ↓reduceIte, ih facts.2, facts.1, List.mem_cons_self, Rat.add_zero]
    · rw [listSum, ih facts.2]
      by_cases member : selected ∈ rest
      · simp [same, member, Rat.zero_add]
      · have different : selected ≠ item := Ne.symm same
        simp [same, member, different, Rat.zero_add]

/-- The exact total of a function with finite support. -/
def HasSum (value : α → Rat) (result : Rat) : Prop :=
  ∃ items : List α, items.Nodup ∧ (∀ item, value item ≠ 0 → item ∈ items) ∧ listSum items value = result

/-- A support list restores any selected function value by a Kronecker sum. -/
theorem listSum_delta [DecidableEq α] (items : List α) (unique : items.Nodup)
    (value : α → Rat) (covers : ∀ item, value item ≠ 0 → item ∈ items) (selected : α) :
    listSum items (fun item => if item = selected then value selected else 0) = value selected := by
  rw [listSum_single items unique]
  split
  · rfl
  · next absent =>
    by_cases hz : value selected = 0
    · exact hz.symm
    · exact False.elim (absent (covers selected hz))

/-- Every finite support witness gives the same total. -/
theorem unique [DecidableEq α] {value : α → Rat} {left right : Rat}
    (hl : HasSum value left) (hr : HasSum value right) : left = right := by
  obtain ⟨ls, lu, lc, le⟩ := hl
  obtain ⟨rs, ru, rc, re⟩ := hr
  rw [← le, ← re]
  calc
    listSum ls value = listSum ls (fun a => listSum rs (fun b => if b = a then value a else 0)) := by
      apply listSum_congr
      intro a ha
      exact (listSum_delta rs ru value rc a).symm
    _ = listSum rs (fun b => listSum ls (fun a => if b = a then value a else 0)) := listSum_exchange _ _ _
    _ = listSum rs value := by
      apply listSum_congr
      intro b hb
      have same : listSum ls (fun a => if b = a then value a else 0) =
          listSum ls (fun a => if a = b then value b else 0) := by
        apply listSum_congr
        intro a ha
        by_cases equal : a = b
        · subst a; rfl
        · have reverse : b ≠ a := Ne.symm equal
          simp [equal, reverse]
      rw [same, listSum_delta ls lu value lc b]

/-- Every duplicate-free support cover computes the declared total. -/
theorem of_cover [DecidableEq α] {value : α → Rat} {result : Rat} (sum : HasSum value result)
    (items : List α) (uniqueItems : items.Nodup) (covers : ∀ item, value item ≠ 0 → item ∈ items) :
    listSum items value = result := unique ⟨items, uniqueItems, covers, rfl⟩ sum

/-- The zero function has total zero. -/
theorem zero : HasSum (fun _ : α => 0) 0 := by
  refine ⟨[], List.nodup_nil, ?_, rfl⟩
  intro item nonzero
  exact False.elim (nonzero rfl)

/-- Merge support witnesses while retaining only the first occurrence of a value. -/
def supportUnion [DecidableEq α] (left right : List α) : List α :=
  left ++ right.filter (fun item => decide (item ∉ left))

theorem supportUnion_unique [DecidableEq α] (left right : List α) (hl : left.Nodup) (hr : right.Nodup) :
    (supportUnion left right).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨hl, hr.filter _, ?_⟩
  intro a ha b hb same
  have absent := of_decide_eq_true (List.mem_filter.mp hb).2
  exact absent (same ▸ ha)

theorem supportUnion_left [DecidableEq α] (left right : List α) {item : α} (member : item ∈ left) :
    item ∈ supportUnion left right := List.mem_append.mpr (Or.inl member)

theorem supportUnion_right [DecidableEq α] (left right : List α) {item : α} (member : item ∈ right) :
    item ∈ supportUnion left right := by
  by_cases present : item ∈ left
  · exact supportUnion_left left right present
  · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨member, by simp [present]⟩))

/-- Exact finite sums add, including functions with overlapping support. -/
theorem add [DecidableEq α] {left right : α → Rat} {ls rs : Rat}
    (hl : HasSum left ls) (hr : HasSum right rs) : HasSum (fun item => left item + right item) (ls + rs) := by
  obtain ⟨l, lu, lc, le⟩ := hl
  obtain ⟨r, ru, rc, re⟩ := hr
  have uniqueItems := supportUnion_unique l r lu ru
  have leftCover : ∀ item, left item ≠ 0 → item ∈ supportUnion l r := fun item nonzero =>
    supportUnion_left l r (lc item nonzero)
  have rightCover : ∀ item, right item ≠ 0 → item ∈ supportUnion l r := fun item nonzero =>
    supportUnion_right l r (rc item nonzero)
  refine ⟨supportUnion l r, uniqueItems, ?_, ?_⟩
  · intro item nonzero
    dsimp only at nonzero
    by_cases leftZero : left item = 0
    · have rightNonzero : right item ≠ 0 := by intro hz; rw [leftZero, hz, Rat.add_zero] at nonzero; exact nonzero rfl
      exact rightCover item rightNonzero
    · exact leftCover item leftZero
  · rw [listSum_add, of_cover ⟨l, lu, lc, le⟩ _ uniqueItems leftCover,
      of_cover ⟨r, ru, rc, re⟩ _ uniqueItems rightCover]

/-- Finite sums commute with finite addition of functions. -/
theorem listSum_hasSum [DecidableEq α] (items : List β) (value : β → α → Rat) (result : β → Rat)
    (sums : ∀ item ∈ items, HasSum (value item) (result item)) :
    HasSum (fun point => listSum items (fun item => value item point)) (listSum items result) := by
  induction items with
  | nil => exact zero
  | cons item rest ih =>
    exact add (sums item (by simp)) (ih (fun item member => sums item (by simp [member])))

/-- Concrete integer interval enumeration. -/
def interval (start : Int) (count : Nat) : List Int :=
  (List.range count).map fun k : Nat => start + (k : Int)

/-- Distinct integer offsets give distinct points. -/
theorem interval_unique (start : Int) (count : Nat) : (interval start count).Nodup := by
  unfold interval
  change List.Pairwise (fun a b : Int => a ≠ b) _
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_range (n := count))
  intro a b different same
  exact different (by omega)

/-- Interval enumeration contains every integer between its inclusive endpoints. -/
theorem interval_covers (low high value : Int) (hl : low ≤ value) (hh : value ≤ high) :
    value ∈ interval low (high - low + 1).toNat := by
  apply List.mem_map.mpr
  refine ⟨(value - low).toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    have first := Int.toNat_of_nonneg (show 0 ≤ value - low by omega)
    have second := Int.toNat_of_nonneg (show 0 ≤ high - low + 1 by omega)
    omega
  · have offset := Int.toNat_of_nonneg (show 0 ≤ value - low by omega)
    omega

/-- Summing the explicit interval list is the source's interval-sum recursion. -/
theorem interval_listSum (value : Int → Rat) (start : Int) (count : Nat) :
    listSum (interval start count) value = Lattice.intervalSum value start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    unfold interval
    rw [List.range_succ, List.map_append, listSum_append]
    change listSum (interval start count) value + (value (start + count) + 0) = _
    rw [ih, Rat.add_zero]
    rfl

/-- An enclosing integer interval supplies an exact finite-support sum. -/
theorem of_interval (value : Int → Rat) (low high : Int)
    (covers : ∀ point, value point ≠ 0 → low ≤ point ∧ point ≤ high) :
    HasSum value (Lattice.intervalSum value low (high - low + 1).toNat) := by
  refine ⟨interval low (high - low + 1).toNat, interval_unique _ _, ?_, interval_listSum _ _ _⟩
  intro point nonzero
  have bounded := covers point nonzero
  exact interval_covers low high point bounded.1 bounded.2

/-- Pointwise equality preserves a finite-support sum. -/
theorem congr {left right : α → Rat} {result : Rat} (sum : HasSum left result)
    (same : ∀ point, left point = right point) : HasSum right result := by
  have equal : left = right := funext same
  rw [← equal]
  exact sum

/-- A finite sum of natural-number values is itself a natural-number value. -/
theorem natural {value : α → Rat} {result : Rat} (sum : HasSum value result)
    (values : ∀ point, ∃ n : Nat, value point = (n : Rat)) : ∃ n : Nat, result = (n : Rat) := by
  obtain ⟨items, uniqueItems, cover, rfl⟩ := sum
  clear uniqueItems cover
  induction items with
  | nil => exact ⟨0, rfl⟩
  | cons item rest ih =>
    obtain ⟨head, headValue⟩ := values item
    obtain ⟨tail, tailValue⟩ := ih
    refine ⟨head + tail, ?_⟩
    rw [listSum, headValue, tailValue, Rat.natCast_add]

/-- Finite sums of nonnegative values are nonnegative. -/
theorem nonnegative {value : α → Rat} {result : Rat} (sum : HasSum value result)
    (values : ∀ point, 0 ≤ value point) : 0 ≤ result := by
  obtain ⟨items, uniqueItems, cover, rfl⟩ := sum
  clear uniqueItems cover
  induction items with
  | nil => change (0 : Rat) ≤ 0; decide
  | cons item rest ih => exact Rat.add_nonneg (values item) ih

end MicroCFTA.FiniteSum
