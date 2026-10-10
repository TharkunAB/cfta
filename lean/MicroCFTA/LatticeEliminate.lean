import MicroCFTA.PolynomialSum

/-!
# Exact first-bound partition for one-variable elimination

The source enumerates every lower-bound and upper-bound pair. It uses strict
comparison against earlier bounds to assign ties to the first bound. This
file verifies that finite enumeration and its weighted interpretation.
Normalization and feasibility filtering are separate operations.
-/

namespace MicroCFTA.LatticeEliminate

open LatticePolynomial

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩
local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

/-- Earlier bounds require a strict improvement, as in `strictBefore`. -/
def strictBefore (chosen current : Nat) (difference : Int) : Int :=
  if current < chosen then difference - 1 else difference

/-- The chosen lower bound must dominate every other lower bound. -/
def lowerRegion (values : List Int) (chosen : Nat) : Bool :=
  (List.range values.length).all fun current =>
    current == chosen || decide (0 ≤ strictBefore chosen current (values.getD chosen 0 - values.getD current 0))

/-- The chosen upper bound must precede every other upper bound. -/
def upperRegion (values : List Int) (chosen : Nat) : Bool :=
  (List.range values.length).all fun current =>
    current == chosen || decide (0 ≤ strictBefore chosen current (values.getD current 0 - values.getD chosen 0))

/-- The exact guard used for one pair after evaluating its linear forms. -/
def pairRegion (lowers uppers : List Int) (indices : Nat × Nat) : Bool :=
  lowerRegion lowers indices.1 && upperRegion uppers indices.2 &&
    decide (lowers.getD indices.1 0 ≤ uppers.getD indices.2 0)

/-- The nested index enumeration from the source. -/
def candidatePairs (lowers uppers : List Int) : List (Nat × Nat) :=
  (List.range lowers.length).flatMap fun low => (List.range uppers.length).map fun high => (low, high)

/-- Keep the pairs whose evaluated region is true. -/
def selectedPairs (lowers uppers : List Int) : List (Nat × Nat) :=
  (candidatePairs lowers uppers).filter (pairRegion lowers uppers)

/-- The lower-bound guard is precisely the first maximum rule. -/
theorem lowerRegion_iff (values : List Int) (chosen : Nat) (valid : chosen < values.length) :
    lowerRegion values chosen = true ↔ Lattice.FirstMaximum (fun k => values.getD k 0) values.length chosen := by
  simp only [lowerRegion, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro guard
    refine ⟨valid, ?_⟩
    intro current hc
    have selected := guard current hc
    dsimp only at selected ⊢
    rcases selected with same | selected
    · subst current; simp
    · unfold strictBefore at selected
      split at selected <;> split <;> omega
  · intro maximum current hc
    have selected := maximum.2 current hc
    dsimp only at selected ⊢
    by_cases same : current = chosen
    · exact Or.inl same
    · right
      unfold strictBefore
      split <;> split at selected <;> omega

/-- The upper-bound guard is the first maximum after negating all values. -/
theorem upperRegion_iff (values : List Int) (chosen : Nat) (valid : chosen < values.length) :
    upperRegion values chosen = true ↔ Lattice.FirstMaximum (fun k => -values.getD k 0) values.length chosen := by
  simp only [upperRegion, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro guard
    refine ⟨valid, ?_⟩
    intro current hc
    have selected := guard current hc
    dsimp only at selected ⊢
    rcases selected with same | selected
    · subst current; simp
    · unfold strictBefore at selected
      split at selected <;> split <;> omega
  · intro maximum current hc
    have selected := maximum.2 current hc
    dsimp only at selected ⊢
    by_cases same : current = chosen
    · exact Or.inl same
    · right
      unfold strictBefore
      split <;> split at selected <;> omega

/-- Every nonempty bound list has exactly one region selected by the tie rule. -/
theorem best_bounds_exist (lowers uppers : List Int)
    (hl : 0 < lowers.length) (hu : 0 < uppers.length) :
    ∃ low high, low < lowers.length ∧ high < uppers.length ∧
      lowerRegion lowers low = true ∧ upperRegion uppers high = true := by
  obtain ⟨low, lower⟩ := Lattice.firstMaximum_exists (fun k => lowers.getD k 0) lowers.length hl
  obtain ⟨high, upper⟩ := Lattice.firstMaximum_exists (fun k => -uppers.getD k 0) uppers.length hu
  exact ⟨low, high, lower.1, upper.1, (lowerRegion_iff lowers low lower.1).mpr lower,
    (upperRegion_iff uppers high upper.1).mpr upper⟩

/-- A candidate pair occurs exactly when both indices are in range. -/
theorem candidatePairs_mem (lowers uppers : List Int) (low high : Nat) :
    (low, high) ∈ candidatePairs lowers uppers ↔ low < lowers.length ∧ high < uppers.length := by
  simp [candidatePairs, List.mem_flatMap, List.mem_map]

/-- Two true pair guards cannot select different bounds. -/
theorem pairRegion_unique (lowers uppers : List Int) (left right : Nat × Nat)
    (hl : left ∈ candidatePairs lowers uppers) (hr : right ∈ candidatePairs lowers uppers)
    (gl : pairRegion lowers uppers left = true) (gr : pairRegion lowers uppers right = true) : left = right := by
  have leftRange := (candidatePairs_mem lowers uppers left.1 left.2).mp hl
  have rightRange := (candidatePairs_mem lowers uppers right.1 right.2).mp hr
  simp only [pairRegion, Bool.and_eq_true, decide_eq_true_eq] at gl gr
  have low := Lattice.firstMaximum_unique (fun k => lowers.getD k 0) lowers.length left.1 right.1
    ((lowerRegion_iff lowers left.1 leftRange.1).mp gl.1.1)
    ((lowerRegion_iff lowers right.1 rightRange.1).mp gr.1.1)
  have high := Lattice.firstMaximum_unique (fun k => -uppers.getD k 0) uppers.length left.2 right.2
    ((upperRegion_iff uppers left.2 leftRange.2).mp gl.1.2)
    ((upperRegion_iff uppers right.2 rightRange.2).mp gr.1.2)
  exact Prod.ext low high

/-- The best lower and upper values describe exactly the original interval constraints. -/
theorem bounds_interval (lowers uppers : List Int) (low high : Nat)
    (hl : low < lowers.length) (hu : high < uppers.length)
    (gl : lowerRegion lowers low = true) (gu : upperRegion uppers high = true) (value : Int) :
    ((∀ i, i < lowers.length → lowers.getD i 0 ≤ value) ∧
      (∀ i, i < uppers.length → value ≤ uppers.getD i 0)) ↔
      lowers.getD low 0 ≤ value ∧ value ≤ uppers.getD high 0 := by
  constructor
  · intro allBounds
    exact ⟨allBounds.1 low hl, allBounds.2 high hu⟩
  · intro interval
    constructor
    · intro i hi
      have comparison := ((lowerRegion_iff lowers low hl).mp gl).2 i hi
      dsimp only at comparison
      split at comparison <;> omega
    · intro i hi
      have comparison := ((upperRegion_iff uppers high hu).mp gu).2 i hi
      dsimp only at comparison
      split at comparison <;> omega

/-- Summing a filtered list equals zeroing its rejected entries. -/
theorem sum_filter (predicate : α → Bool) (weight : α → Rat) (items : List α) :
    ((items.filter predicate).map weight).sum =
      (items.map fun item => if predicate item then weight item else 0).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases hp : predicate item <;> simp [hp, ih, Rat.zero_add]

/-- The list enumeration has the same value as the nested finite sums. -/
theorem sum_candidatePairs (lowers uppers : List Int) (weight : Nat × Nat → Rat) :
    ((candidatePairs lowers uppers).map weight).sum =
      Faulhaber.sum lowers.length (fun low => Faulhaber.sum uppers.length (fun high => weight (low, high))) := by
  unfold candidatePairs
  have flatten (items : List Nat) :
      ((items.flatMap fun low => (List.range uppers.length).map fun high => (low, high)).map weight).sum =
        (items.map fun low => Faulhaber.sum uppers.length (fun high => weight (low, high))).sum := by
    induction items with
    | nil => rfl
    | cons item rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def, Faulhaber.sum_range, ih]
  rw [flatten, Faulhaber.sum_range]

/-- True regions contribute one interval; every other enumerated pair contributes zero. -/
theorem selected_weight (lowers uppers : List Int) (weight : Nat × Nat → Rat) (low high : Nat)
    (hl : low < lowers.length) (hu : high < uppers.length)
    (gl : lowerRegion lowers low = true) (gu : upperRegion uppers high = true) :
    ((selectedPairs lowers uppers).map weight).sum =
      if lowers.getD low 0 ≤ uppers.getD high 0 then weight (low, high) else 0 := by
  unfold selectedPairs
  rw [sum_filter, sum_candidatePairs]
  have outer : Faulhaber.sum lowers.length (fun li => Faulhaber.sum uppers.length
      (fun hi => if pairRegion lowers uppers (li, hi) then weight (li, hi) else 0)) =
      Faulhaber.sum lowers.length (fun li => if li = low then
        (if lowers.getD low 0 ≤ uppers.getD high 0 then weight (low, high) else 0) else 0) := by
    apply Faulhaber.sum_congr
    intro li hli
    have inner : Faulhaber.sum uppers.length
        (fun hi => if pairRegion lowers uppers (li, hi) then weight (li, hi) else 0) =
        Faulhaber.sum uppers.length (fun hi => if hi = high then
          (if li = low then (if lowers.getD low 0 ≤ uppers.getD high 0 then weight (low, high) else 0) else 0)
          else 0) := by
      apply Faulhaber.sum_congr
      intro hi hhi
      by_cases sameLow : li = low
      · subst li
        by_cases sameHigh : hi = high
        · subst hi; simp [pairRegion, gl, gu]
        · have rejected : upperRegion uppers hi ≠ true := by
            intro other
            have unique := Lattice.firstMaximum_unique (fun k => -uppers.getD k 0) uppers.length hi high
              ((upperRegion_iff uppers hi hhi).mp other) ((upperRegion_iff uppers high hu).mp gu)
            exact sameHigh unique
          simp [pairRegion, rejected, sameHigh]
      · have rejected : lowerRegion lowers li ≠ true := by
          intro other
          have unique := Lattice.firstMaximum_unique (fun k => lowers.getD k 0) lowers.length li low
            ((lowerRegion_iff lowers li hli).mp other) ((lowerRegion_iff lowers low hl).mp gl)
          exact sameLow unique
        simp [pairRegion, rejected, sameLow]
    rw [inner, Faulhaber.sum_single]
    simp only [hu, ↓reduceIte]
  rw [outer, Faulhaber.sum_single]
  simp only [hl, ↓reduceIte]

/-- Every satisfying integer is covered by exactly one generated bound pair. -/
theorem selectedPairs_cover (lowers uppers : List Int)
    (hl : 0 < lowers.length) (hu : 0 < uppers.length) (value : Int) :
    ((∀ i, i < lowers.length → lowers.getD i 0 ≤ value) ∧
      (∀ i, i < uppers.length → value ≤ uppers.getD i 0)) ↔
      ∃ indices, indices ∈ selectedPairs lowers uppers ∧
        lowers.getD indices.1 0 ≤ value ∧ value ≤ uppers.getD indices.2 0 ∧
        ∀ other, other ∈ selectedPairs lowers uppers → other = indices := by
  constructor
  · intro satisfies
    obtain ⟨low, high, lowRange, highRange, gl, gu⟩ := best_bounds_exist lowers uppers hl hu
    have interval := (bounds_interval lowers uppers low high lowRange highRange gl gu value).mp satisfies
    have region : pairRegion lowers uppers (low, high) = true := by
      simp only [pairRegion, gl, gu, Bool.true_and, decide_eq_true_eq]
      omega
    have candidate : (low, high) ∈ candidatePairs lowers uppers :=
      (candidatePairs_mem lowers uppers low high).mpr ⟨lowRange, highRange⟩
    refine ⟨(low, high), List.mem_filter.mpr ⟨candidate, region⟩, interval.1, interval.2, ?_⟩
    intro other member
    have selected := List.mem_filter.mp member
    exact pairRegion_unique lowers uppers other (low, high) selected.1 candidate selected.2 region
  · rintro ⟨indices, member, low, high, unique⟩
    have selected := List.mem_filter.mp member
    have ranges := (candidatePairs_mem lowers uppers indices.1 indices.2).mp selected.1
    have regions := selected.2
    simp only [pairRegion, Bool.and_eq_true, decide_eq_true_eq] at regions
    exact (bounds_interval lowers uppers indices.1 indices.2 ranges.1 ranges.2
      regions.1.1 regions.1.2 value).mpr ⟨low, high⟩

/-- Rational polynomial weights are exact after selecting their bound pair. -/
theorem selected_sumOver (assignment : Nat → Rat) (index : Nat) (polynomial : Polynomial)
    (lowerForms upperForms : List Linear) (lowers uppers : List Int)
    (low high : Nat) (hl : low < lowers.length) (hu : high < uppers.length)
    (gl : lowerRegion lowers low = true) (gu : upperRegion uppers high = true)
    (lowerValue : ∀ i, i < lowers.length →
      evaluateLinear assignment (lowerForms.getD i ⟨[], 0⟩) = (lowers.getD i 0 : Rat))
    (upperValue : ∀ i, i < uppers.length →
      evaluateLinear assignment (upperForms.getD i ⟨[], 0⟩) = (uppers.getD i 0 : Rat))
    (ordered : OrderedMonomials polynomial) :
    ((selectedPairs lowers uppers).map fun indices =>
      evaluate assignment (PolynomialSum.sumOver index
        (lowerForms.getD indices.1 ⟨[], 0⟩) (upperForms.getD indices.2 ⟨[], 0⟩) polynomial)).sum =
      Lattice.intervalSum (fun value => evaluate (PolynomialSum.update assignment index (value : Rat)) polynomial)
        (lowers.getD low 0) (uppers.getD high 0 - lowers.getD low 0 + 1).toNat := by
  rw [selected_weight lowers uppers _ low high hl hu gl gu]
  split
  · next nonempty =>
    exact PolynomialSum.evaluate_sumOver assignment index _ _ polynomial _ _
      (lowerValue low hl) (upperValue high hu) (by omega) ordered
  · next empty =>
    have countZero : (uppers.getD high 0 - lowers.getD low 0 + 1).toNat = 0 := by omega
    rw [countZero]
    rfl

end MicroCFTA.LatticeEliminate
