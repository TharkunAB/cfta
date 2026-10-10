import Std

/-!
# Finite sparse counts and masses

The executable merge, convolution, and lookup follow `addSparse`, `mulSparse`,
and `valueAtSize` in `Ranked/Internal/Size.hs`. The algebra applies to both
natural counts and rational masses. A series has strictly increasing sizes.
Zero coefficients are allowed. This module concerns finite lists; it does not
prove productivity of Haskell's lazy infinite series.
-/

namespace MicroCFTA.Sparse

open Lean.Grind

/-- Sparse coefficients indexed by a nonnegative size. -/
abbrev Series (α : Type) := List (Nat × α)

/-- The denotation sums every coefficient with the requested size. -/
def coefficient [Semiring α] : Series α → Nat → α
  | [], _ => 0
  | (size, value) :: rest, wanted =>
      (if size = wanted then value else 0) + coefficient rest wanted

/-- Merge two sparse series by comparing their first sizes. -/
def addSparse [Add α] : Series α → Series α → Series α
  | [], right => right
  | left, [] => left
  | (ls, lv) :: left, (rs, rv) :: right =>
      if ls < rs then (ls, lv) :: addSparse left ((rs, rv) :: right)
      else if rs < ls then (rs, rv) :: addSparse ((ls, lv) :: left) right
      else (ls, lv + rv) :: addSparse left right
termination_by left right => left.length + right.length

/-- Shift the sizes and multiply the coefficients by one term. -/
def shiftScale [Mul α] (size : Nat) (value : α) (series : Series α) : Series α :=
  series.map fun (s, v) => (size + s, value * v)

/-- Convolve sparse series in the same head-first order as the Haskell worker. -/
def mulSparse [Semiring α] : Series α → Series α → Series α
  | [], _ => []
  | _, [] => []
  | (ls, lv) :: left, (rs, rv) :: right =>
      (ls + rs, lv * rv) ::
        addSparse (shiftScale ls lv right) (mulSparse left ((rs, rv) :: right))

/-- Strict order prevents duplicate sizes from hiding behind a lookup. -/
def Ordered (series : Series α) : Prop := series.Pairwise (fun a b => a.1 < b.1)

/-- The sparse lookup stops at the first size that is not smaller. -/
def valueAtSize [Semiring α] : Series α → Nat → α
  | [], _ => 0
  | (size, value) :: rest, wanted =>
      if size < wanted then valueAtSize rest wanted
      else if size = wanted then value else 0

/-- Merging retains the sum of coefficients, even before the ordering invariant. -/
theorem coefficient_addSparse [Semiring α] (left right : Series α) (size : Nat) :
    coefficient (addSparse left right) size = coefficient left size + coefficient right size := by
  fun_induction addSparse left right with
  | case1 right => simp [coefficient]; grind
  | case2 head tail => simp [coefficient]; grind
  | case3 ls lv left rs rv right h ih =>
    simp only [coefficient, ih]
    grind
  | case4 ls lv left rs rv right h h' ih =>
    simp only [coefficient, ih]
    grind
  | case5 ls lv left rs rv right h h' ih =>
    have he : ls = rs := by omega
    subst rs
    simp only [coefficient, ih]
    split <;> grind

/-- A size strictly below every entry has coefficient zero. -/
theorem coefficient_below [Semiring α] (series : Series α) (wanted : Nat)
    (h : ∀ entry ∈ series, wanted < entry.1) : coefficient series wanted = 0 := by
  induction series with
  | nil => rfl
  | cons entry rest ih =>
    have he := h entry (by simp)
    have hr := ih (fun e hm => h e (by simp [hm]))
    simp only [coefficient, hr]
    have hn : entry.1 ≠ wanted := by omega
    simp [hn]
    grind

/-- Ordered sparse lookup equals the complete coefficient sum. -/
theorem valueAtSize_correct [Semiring α] (series : Series α) (ordered : Ordered series)
    (wanted : Nat) : valueAtSize series wanted = coefficient series wanted := by
  induction series with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨size, value⟩
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    by_cases hlt : size < wanted
    · have hne : size ≠ wanted := by omega
      simp [valueAtSize, hlt, coefficient, hne, ih tailOrdered]
      grind
    · by_cases heq : size = wanted
      · subst wanted
        have hz := coefficient_below rest size headBefore
        simp [valueAtSize, coefficient, hz]
        grind
      · have hz := coefficient_below rest wanted (by
          intro e he
          have hp := headBefore e he
          omega)
        simp [valueAtSize, coefficient, hlt, heq, hz]
        grind

/-- The entries emitted by a merge use only sizes present in its inputs. -/
theorem addSparse_sizes [Add α] (left right : Series α) (entry : Nat × α)
    (h : entry ∈ addSparse left right) :
    (∃ e ∈ left, e.1 = entry.1) ∨ ∃ e ∈ right, e.1 = entry.1 := by
  fun_induction addSparse left right with
  | case1 right => exact Or.inr ⟨entry, h, rfl⟩
  | case2 head tail => exact Or.inl ⟨entry, h, rfl⟩
  | case3 ls lv left rs rv right hlt ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst entry; exact Or.inl ⟨(ls, lv), by simp, rfl⟩
    · rcases ih ht with hl | hr
      · obtain ⟨e, he, hk⟩ := hl
        exact Or.inl ⟨e, by simp [he], hk⟩
      · exact Or.inr hr
  | case4 ls lv left rs rv right hlt hgt ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst entry; exact Or.inr ⟨(rs, rv), by simp, rfl⟩
    · rcases ih ht with hl | hr
      · exact Or.inl hl
      · obtain ⟨e, he, hk⟩ := hr
        exact Or.inr ⟨e, by simp [he], hk⟩
  | case5 ls lv left rs rv right hlt hgt ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst entry; exact Or.inl ⟨(ls, lv), by simp, rfl⟩
    · rcases ih ht with hl | hr
      · obtain ⟨e, he, hk⟩ := hl
        exact Or.inl ⟨e, by simp [he], hk⟩
      · obtain ⟨e, he, hk⟩ := hr
        exact Or.inr ⟨e, by simp [he], hk⟩

/-- The merge preserves strict size order. -/
theorem addSparse_ordered [Add α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right) : Ordered (addSparse left right) := by
  fun_induction addSparse left right with
  | case1 right => exact hr
  | case2 head tail => exact hl
  | case3 ls lv left rs rv right hlt ih =>
    obtain ⟨hleft, otl⟩ := List.pairwise_cons.mp hl
    obtain ⟨hright, otr⟩ := List.pairwise_cons.mp hr
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih otl hr⟩
    intro e he
    rcases addSparse_sizes left ((rs, rv) :: right) e he with h | h
    · obtain ⟨x, hx, hk⟩ := h
      have := hleft x hx
      omega
    · obtain ⟨x, hx, hk⟩ := h
      rcases List.mem_cons.mp hx with hx | hx
      · subst x; omega
      · have := hright x hx; omega
  | case4 ls lv left rs rv right hlt hgt ih =>
    obtain ⟨hleft, otl⟩ := List.pairwise_cons.mp hl
    obtain ⟨hright, otr⟩ := List.pairwise_cons.mp hr
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hl otr⟩
    intro e he
    rcases addSparse_sizes ((ls, lv) :: left) right e he with h | h
    · obtain ⟨x, hx, hk⟩ := h
      rcases List.mem_cons.mp hx with hx | hx
      · subst x; omega
      · have := hleft x hx; omega
    · obtain ⟨x, hx, hk⟩ := h
      have := hright x hx
      omega
  | case5 ls lv left rs rv right hlt hgt ih =>
    obtain ⟨hleft, otl⟩ := List.pairwise_cons.mp hl
    obtain ⟨hright, otr⟩ := List.pairwise_cons.mp hr
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih otl otr⟩
    intro e he
    rcases addSparse_sizes left right e he with h | h
    · obtain ⟨x, hx, hk⟩ := h
      have := hleft x hx
      omega
    · obtain ⟨x, hx, hk⟩ := h
      have := hright x hx
      omega

/-- A shift retains the strict ordering of sizes, including when the shift is zero. -/
theorem shiftScale_ordered [Mul α] (size : Nat) (value : α) (series : Series α)
    (h : Ordered series) : Ordered (shiftScale size value series) := by
  apply List.pairwise_map.mpr
  exact h.imp (by intro a b hab; simp; omega)

/-- Every convolution entry has the sum of sizes from its two inputs. -/
theorem mulSparse_sizes [Semiring α] (left right : Series α) (entry : Nat × α)
    (h : entry ∈ mulSparse left right) :
    ∃ l ∈ left, ∃ r ∈ right, entry.1 = l.1 + r.1 := by
  induction left generalizing right entry with
  | nil => simp [mulSparse] at h
  | cons l left ih =>
    cases right with
    | nil => simp [mulSparse] at h
    | cons r right =>
      rcases l with ⟨ls, lv⟩
      rcases r with ⟨rs, rv⟩
      rcases List.mem_cons.mp h with he | ht
      · subst entry
        exact ⟨(ls, lv), by simp, (rs, rv), by simp, rfl⟩
      · rcases addSparse_sizes _ _ entry ht with hs | hm
        · obtain ⟨e, he, hk⟩ := hs
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
          exact ⟨(ls, lv), by simp, r, by simp [hr], hk.symm⟩
        · obtain ⟨e, he, hk⟩ := hm
          obtain ⟨l, hl, r, hr, heq⟩ := ih ((rs, rv) :: right) e he
          exact ⟨l, by simp [hl], r, hr, hk.symm.trans heq⟩

/-- Convolution preserves the strict ordering required by sparse lookup. -/
theorem mulSparse_ordered [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right) : Ordered (mulSparse left right) := by
  induction left generalizing right with
  | nil => simp [mulSparse, Ordered]
  | cons l left ih =>
    cases right with
    | nil => simp [mulSparse, Ordered]
    | cons r right =>
      rcases l with ⟨ls, lv⟩
      rcases r with ⟨rs, rv⟩
      obtain ⟨hleft, otl⟩ := List.pairwise_cons.mp hl
      obtain ⟨hright, otr⟩ := List.pairwise_cons.mp hr
      apply List.pairwise_cons.mpr
      refine ⟨?_, addSparse_ordered _ _ (shiftScale_ordered ls lv right otr) (ih _ otl hr)⟩
      intro e he
      rcases addSparse_sizes _ _ e he with hs | hm
      · obtain ⟨x, hx, hk⟩ := hs
        obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hx
        have := hright r hmem
        change ls + r.1 = e.1 at hk
        omega
      · obtain ⟨x, hx, hk⟩ := hm
        obtain ⟨l, hmeml, r, hmemr, heq⟩ := mulSparse_sizes _ _ x hx
        have hlt := hleft l hmeml
        rcases List.mem_cons.mp hmemr with he | he
        · subst r; omega
        · have hrt := hright r he; omega

/-- Independent convolution semantics: sum the shifted rows without merging them. -/
def convolution [Semiring α] : Series α → Series α → Nat → α
  | [], _, _ => 0
  | (size, value) :: left, right, wanted =>
      coefficient (shiftScale size value right) wanted + convolution left right wanted

/-- The sparse convolution equals the complete Cartesian convolution. -/
theorem coefficient_mulSparse [Semiring α] (left right : Series α) (wanted : Nat) :
    coefficient (mulSparse left right) wanted = convolution left right wanted := by
  induction left generalizing right with
  | nil => rfl
  | cons l left ih =>
    cases right with
    | nil =>
      have hempty : ∀ xs : Series α, convolution xs [] wanted = 0 := by
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [convolution, shiftScale, coefficient, ih]; grind
      simp [mulSparse, coefficient, hempty]
    | cons r right =>
      rcases l with ⟨ls, lv⟩
      rcases r with ⟨rs, rv⟩
      simp only [mulSparse, coefficient, coefficient_addSparse, ih, convolution,
        shiftScale, List.map_cons]
      grind

/-- The implemented lookup of merged series has the intended pointwise sum. -/
theorem valueAtSize_addSparse [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right) (size : Nat) :
    valueAtSize (addSparse left right) size = valueAtSize left size + valueAtSize right size := by
  rw [valueAtSize_correct _ (addSparse_ordered _ _ hl hr), coefficient_addSparse,
    valueAtSize_correct _ hl, valueAtSize_correct _ hr]

/-- The implemented lookup of a sparse product has the full convolution mass. -/
theorem valueAtSize_mulSparse [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right) (size : Nat) :
    valueAtSize (mulSparse left right) size = convolution left right size := by
  rw [valueAtSize_correct _ (mulSparse_ordered _ _ hl hr), coefficient_mulSparse]

/-- A leading size-one zero is safe when every product size is strictly larger. -/
theorem seeded_product_ordered [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right)
    (positiveLeft : ∀ e ∈ left, 1 ≤ e.1)
    (positiveRight : ∀ e ∈ right, 1 ≤ e.1) :
    Ordered ((1, (0 : α)) :: mulSparse left right) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, mulSparse_ordered left right hl hr⟩
  intro e he
  obtain ⟨l, hl', r, hr', heq⟩ := mulSparse_sizes left right e he
  have := positiveLeft l hl'
  have := positiveRight r hr'
  omega

/-- Under the positive-size condition, the recursive seed changes no coefficient. -/
theorem seeded_product_correct [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right)
    (positiveLeft : ∀ e ∈ left, 1 ≤ e.1)
    (positiveRight : ∀ e ∈ right, 1 ≤ e.1) (size : Nat) :
    valueAtSize ((1, (0 : α)) :: mulSparse left right) size = convolution left right size := by
  rw [valueAtSize_correct _ (seeded_product_ordered left right hl hr positiveLeft positiveRight)]
  simp only [coefficient, ite_self, coefficient_mulSparse]
  grind

/-- A size-one seed hides a genuine size-zero coefficient. -/
theorem zero_seed_counterexample :
    valueAtSize ((1, 0) :: mulSparse (α := Nat) [(0, 1)] [(0, 1)]) 0 = 0 ∧
    convolution (α := Nat) [(0, 1)] [(0, 1)] 0 = 1 := by decide

/-- A duplicate size-one seed hides the genuine coefficient at size one. -/
theorem duplicate_seed_counterexample :
    valueAtSize ((1, 0) :: mulSparse (α := Nat) [(0, 1)] [(1, 1)]) 1 = 0 ∧
    convolution (α := Nat) [(0, 1)] [(1, 1)] 1 = 1 := by decide

/-- The same sparse arithmetic theorem applies to rational probability masses. -/
theorem rational_convolution (left right : Series Rat)
    (hl : Ordered left) (hr : Ordered right) (size : Nat) :
    valueAtSize (mulSparse left right) size = convolution left right size :=
  valueAtSize_mulSparse left right hl hr size

/-- A shifted row contributes only at sizes at least its shift. -/
theorem coefficient_shiftScale [Semiring α] (shift : Nat) (factor : α)
    (series : Series α) (wanted : Nat) :
    coefficient (shiftScale shift factor series) wanted =
      if shift ≤ wanted then factor * coefficient series (wanted - shift) else 0 := by
  induction series with
  | nil => simp [shiftScale, coefficient]; grind
  | cons entry rest ih =>
    rcases entry with ⟨size, value⟩
    simp only [shiftScale, List.map_cons, coefficient] at *
    rw [ih]
    by_cases h : shift ≤ wanted
    · have heq : shift + size = wanted ↔ size = wanted - shift := by omega
      simp only [h, ↓reduceIte, heq]
      split <;> grind
    · have hne : shift + size ≠ wanted := by omega
      simp only [h, ↓reduceIte, hne]
      grind

/-- The usual size-split recurrence for a finite convolution. -/
def splitSum [Semiring α] : Series α → Series α → Nat → α
  | [], _, _ => 0
  | (size, value) :: left, right, wanted =>
      (if size ≤ wanted then value * coefficient right (wanted - size) else 0) +
        splitSum left right wanted

/-- The full Cartesian semantics equals the size-split recurrence. -/
theorem convolution_eq_splitSum [Semiring α] (left right : Series α) (wanted : Nat) :
    convolution left right wanted = splitSum left right wanted := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp only [convolution, coefficient_shiftScale, splitSum, ih]

/-- Sparse multiplication and lookup compute the size-split sum exactly. -/
theorem sparse_split_correct [Semiring α] (left right : Series α)
    (hl : Ordered left) (hr : Ordered right) (size : Nat) :
    valueAtSize (mulSparse left right) size = splitSum left right size := by
  rw [valueAtSize_mulSparse left right hl hr, convolution_eq_splitSum]

end MicroCFTA.Sparse
