import MicroCFTA.LatticeBound
import MicroCFTA.LatticeEliminate

/-!
# Raw polynomial piece splitting

A piece has linear inequalities and a polynomial weight. The raw split
constructs every first-bound region before normalization or feasibility
filtering. Each region has the same linear forms and polynomial as the source.
-/

namespace MicroCFTA.LatticePiece

open LatticeLinear

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- A conjunction of inequalities and its rational polynomial weight. -/
structure Piece where
  constraints : List Linear
  polynomial : LatticePolynomial.Polynomial

/-- A conjunction holds when each evaluated form is nonnegative. -/
def holds (assignment : Nat → Int) (constraints : List Linear) : Bool :=
  constraints.all fun linear => decide (0 ≤ evaluate assignment linear)

/-- The value contributed by a piece at one outer assignment. -/
def pieceValue (assignment : Nat → Int) (piece : Piece) : Rat :=
  if holds assignment piece.constraints then
    LatticePolynomial.evaluate (fun index => (assignment index : Rat)) piece.polynomial else 0

/-- Traverse involved constraints and preserve the order within each kind of bound. -/
def collectBounds (index : Nat) : List Linear → Except Unit (List Linear × List Linear)
  | [] => .ok ([], [])
  | linear :: rest => do
    let first ← LatticeBound.bound index linear
    let (lowers, uppers) ← collectBounds index rest
    match first with
    | .inl lower => .ok (lower :: lowers, uppers)
    | .inr upper => .ok (lowers, upper :: uppers)

/-- Successful collection preserves every original inequality. -/
theorem collectBounds_correct (assignment : Nat → Int) (index : Nat) (forms lowers uppers : List Linear)
    (valid : ∀ linear ∈ forms, Valid linear)
    (success : collectBounds index forms = .ok (lowers, uppers)) (value : Int) :
    (∀ linear ∈ forms, 0 ≤ evaluate (LatticeBound.update assignment index value) linear) ↔
      (∀ lower ∈ lowers, evaluate assignment lower ≤ value) ∧
      (∀ upper ∈ uppers, value ≤ evaluate assignment upper) := by
  induction forms generalizing lowers uppers with
  | nil =>
    simp only [collectBounds] at success
    cases success
    simp
  | cons linear rest ih =>
    have headValid := valid linear (by simp)
    have tailValid : ∀ item ∈ rest, Valid item := fun item member => valid item (by simp [member])
    cases first : LatticeBound.bound index linear with
    | error error => simp [collectBounds, first] at success
    | ok firstBound =>
      cases tail : collectBounds index rest with
      | error error => simp [collectBounds, first, tail] at success
      | ok bounds =>
        rcases bounds with ⟨ls, us⟩
        have headCorrect := LatticeBound.bound_correct assignment index linear firstBound headValid first value
        have tailCorrect := ih ls us tailValid tail
        cases firstBound with
        | inl lower =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          simp only [List.forall_mem_cons, headCorrect, tailCorrect]
          exact and_assoc.symm
        | inr upper =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          simp only [List.forall_mem_cons, headCorrect, tailCorrect]
          exact and_left_comm

/-- Successful bounds have canonical coefficient maps and omit the selected variable. -/
theorem collectBounds_metadata (index : Nat) (forms lowers uppers : List Linear)
    (valid : ∀ linear ∈ forms, Valid linear)
    (success : collectBounds index forms = .ok (lowers, uppers)) :
    (∀ lower ∈ lowers, Valid lower ∧ PolynomialSupport.LinearFree index lower) ∧
    (∀ upper ∈ uppers, Valid upper ∧ PolynomialSupport.LinearFree index upper) := by
  induction forms generalizing lowers uppers with
  | nil =>
    simp only [collectBounds] at success
    cases success
    simp
  | cons linear rest ih =>
    have headValid := valid linear (by simp)
    have tailValid : ∀ item ∈ rest, Valid item := fun item member => valid item (by simp [member])
    cases first : LatticeBound.bound index linear with
    | error error => simp [collectBounds, first] at success
    | ok firstBound =>
      cases tail : collectBounds index rest with
      | error error => simp [collectBounds, first, tail] at success
      | ok bounds =>
        rcases bounds with ⟨ls, us⟩
        have headCanonical := LatticeBound.bound_valid index linear firstBound headValid first
        have headFree := LatticeBound.bound_free index linear firstBound first
        have tailMetadata := ih ls us tailValid tail
        cases firstBound with
        | inl lower =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          simp only [List.forall_mem_cons]
          exact ⟨⟨⟨headCanonical, headFree⟩, tailMetadata.1⟩, tailMetadata.2⟩
        | inr upper =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          simp only [List.forall_mem_cons]
          exact ⟨tailMetadata.1, ⟨⟨headCanonical, headFree⟩, tailMetadata.2⟩⟩

/-- The source's strict comparison on linear forms. -/
def strictBefore (chosen current : Nat) (difference : Linear) : Linear :=
  if current < chosen then minus difference (constant 1) else difference

/-- Evaluate all bound forms at the outer assignment. -/
def values (assignment : Nat → Int) (forms : List Linear) : List Int := forms.map (evaluate assignment)

/-- Default-zero map lookup commutes with bound evaluation. -/
theorem values_getD (assignment : Nat → Int) (forms : List Linear) (index : Nat) :
    (values assignment forms).getD index 0 = evaluate assignment (forms.getD index (constant 0)) := by
  induction forms generalizing index with
  | nil => simp [values, evaluate_constant]
  | cons form rest ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index

/-- Linear strict comparison has the integer meaning used by the bound partition. -/
theorem evaluate_strictBefore (assignment : Nat → Int) (chosen current : Nat) (difference : Linear) :
    evaluate assignment (strictBefore chosen current difference) =
      LatticeEliminate.strictBefore chosen current (evaluate assignment difference) := by
  by_cases earlier : current < chosen
  · simp [strictBefore, LatticeEliminate.strictBefore, earlier, evaluate_minus, evaluate_constant]
  · simp [strictBefore, LatticeEliminate.strictBefore, earlier]

/-- Lower-bound dominance forms, excluding comparison with the bound itself. -/
def lowerComparisons (forms : List Linear) (chosen : Nat) : List Linear :=
  ((List.range forms.length).filter fun current => current != chosen).map fun current =>
    strictBefore chosen current (minus (forms.getD chosen (constant 0)) (forms.getD current (constant 0)))

/-- Upper-bound dominance forms, excluding comparison with the bound itself. -/
def upperComparisons (forms : List Linear) (chosen : Nat) : List Linear :=
  ((List.range forms.length).filter fun current => current != chosen).map fun current =>
    strictBefore chosen current (minus (forms.getD current (constant 0)) (forms.getD chosen (constant 0)))

/-- Evaluating generated lower comparisons yields the source's first-maximum guard. -/
theorem holds_lowerComparisons (assignment : Nat → Int) (forms : List Linear) (chosen : Nat) :
    holds assignment (lowerComparisons forms chosen) =
      LatticeEliminate.lowerRegion (values assignment forms) chosen := by
  apply Bool.eq_iff_iff.mpr
  simp only [holds, lowerComparisons, LatticeEliminate.lowerRegion, List.all_map, List.all_filter,
    List.all_eq_true, List.mem_range, Function.comp_def, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, evaluate_strictBefore, evaluate_minus]
  rw [show (values assignment forms).length = forms.length by simp [values]]
  simp only [values_getD]
  simp only [bne, Bool.not_not, beq_iff_eq]

/-- Evaluating generated upper comparisons yields the source's first-minimum guard. -/
theorem holds_upperComparisons (assignment : Nat → Int) (forms : List Linear) (chosen : Nat) :
    holds assignment (upperComparisons forms chosen) =
      LatticeEliminate.upperRegion (values assignment forms) chosen := by
  apply Bool.eq_iff_iff.mpr
  simp only [holds, upperComparisons, LatticeEliminate.upperRegion, List.all_map, List.all_filter,
    List.all_eq_true, List.mem_range, Function.comp_def, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, evaluate_strictBefore, evaluate_minus]
  rw [show (values assignment forms).length = forms.length by simp [values]]
  simp only [values_getD]
  simp only [bne, Bool.not_not, beq_iff_eq]

/-- The linear region attached to one candidate pair in `eliminate`. -/
def region (rest lowers uppers : List Linear) (indices : Nat × Nat) : List Linear :=
  rest ++ lowerComparisons lowers indices.1 ++ upperComparisons uppers indices.2 ++
    [minus (uppers.getD indices.2 (constant 0)) (lowers.getD indices.1 (constant 0))]

theorem holds_append (assignment : Nat → Int) (left right : List Linear) :
    holds assignment (left ++ right) = (holds assignment left && holds assignment right) := List.all_append

/-- The generated linear region is exactly the previously proved bound-pair guard. -/
theorem holds_region (assignment : Nat → Int) (rest lowers uppers : List Linear) (indices : Nat × Nat) :
    holds assignment (region rest lowers uppers indices) =
      (holds assignment rest && LatticeEliminate.pairRegion (values assignment lowers) (values assignment uppers) indices) := by
  unfold region
  rw [holds_append, holds_append, holds_append, holds_lowerComparisons, holds_upperComparisons]
  apply Bool.eq_iff_iff.mpr
  simp only [holds, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    LatticeEliminate.pairRegion, decide_eq_true_eq, evaluate_minus, values_getD]
  have compare :
      (0 ≤ evaluate assignment (uppers.getD indices.2 (constant 0)) - evaluate assignment (lowers.getD indices.1 (constant 0))) ↔
      evaluate assignment (lowers.getD indices.1 (constant 0)) ≤ evaluate assignment (uppers.getD indices.2 (constant 0)) := by omega
  rw [compare]
  simp only [and_assoc]

/-- The source polynomial and raw constraint region for a candidate pair. -/
def pairPiece (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial) (indices : Nat × Nat) : Piece :=
  ⟨region rest lowers uppers indices,
    PolynomialSum.sumOver index (lowers.getD indices.1 (constant 0))
      (uppers.getD indices.2 (constant 0)) polynomial⟩

/-- Enumerate all raw pieces before the source normalizes and rejects regions. -/
def rawPieces (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial) : List Piece :=
  ((List.range lowers.length).flatMap fun low =>
    (List.range uppers.length).map fun high => (low, high)).map (pairPiece index rest lowers uppers polynomial)

/-- One generated piece contributes only when both its residual and selection guards hold. -/
theorem pairPiece_value (assignment : Nat → Int) (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial) (indices : Nat × Nat) :
    pieceValue assignment (pairPiece index rest lowers uppers polynomial indices) =
      if holds assignment rest then
        (if LatticeEliminate.pairRegion (values assignment lowers) (values assignment uppers) indices then
          LatticePolynomial.evaluate (fun i => (assignment i : Rat))
            (PolynomialSum.sumOver index (lowers.getD indices.1 (constant 0))
              (uppers.getD indices.2 (constant 0)) polynomial) else 0)
      else 0 := by
  unfold pieceValue pairPiece
  rw [holds_region]
  cases holds assignment rest <;>
    cases LatticeEliminate.pairRegion (values assignment lowers) (values assignment uppers) indices <;> rfl

/-- The sum of zero values is zero. -/
theorem list_sum_zero (items : List α) : (items.map fun _ => (0 : Rat)).sum = 0 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [ih, Rat.zero_add]

/-- Raw piece interpretation is the selected-pair weighted sum from `LatticeEliminate`. -/
theorem rawPieces_value (assignment : Nat → Int) (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial) :
    ((rawPieces index rest lowers uppers polynomial).map (pieceValue assignment)).sum =
      if holds assignment rest then
        ((LatticeEliminate.selectedPairs (values assignment lowers) (values assignment uppers)).map fun indices =>
          LatticePolynomial.evaluate (fun i => (assignment i : Rat))
            (PolynomialSum.sumOver index (lowers.getD indices.1 (constant 0))
              (uppers.getD indices.2 (constant 0)) polynomial)).sum
      else 0 := by
  unfold rawPieces
  rw [List.map_map]
  simp only [Function.comp_def, pairPiece_value]
  have pairs : ((List.range lowers.length).flatMap fun low => (List.range uppers.length).map fun high => (low, high)) =
      LatticeEliminate.candidatePairs (values assignment lowers) (values assignment uppers) := by
    simp only [LatticeEliminate.candidatePairs, values, List.length_map]
  rw [pairs]
  cases restHolds : holds assignment rest with
  | false => exact list_sum_zero _
  | true =>
    simp only [↓reduceIte]
    exact (LatticeEliminate.sum_filter _ _ _).symm

/-- Actual raw polynomial pieces preserve the finite weighted interval sum. -/
theorem rawPieces_sum (assignment : Nat → Int) (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial) (low high : Nat)
    (hl : low < lowers.length) (hu : high < uppers.length)
    (gl : LatticeEliminate.lowerRegion (values assignment lowers) low = true)
    (gu : LatticeEliminate.upperRegion (values assignment uppers) high = true)
    (ordered : LatticePolynomial.OrderedMonomials polynomial) :
    ((rawPieces index rest lowers uppers polynomial).map (pieceValue assignment)).sum =
      if holds assignment rest then
        Lattice.intervalSum
          (fun value => LatticePolynomial.evaluate
            (fun i => (LatticeBound.update assignment index value i : Rat)) polynomial)
          (evaluate assignment (lowers.getD low (constant 0)))
          (evaluate assignment (uppers.getD high (constant 0)) -
            evaluate assignment (lowers.getD low (constant 0)) + 1).toNat
      else 0 := by
  rw [rawPieces_value]
  split
  · have step := LatticeEliminate.selected_sumOver (fun i => (assignment i : Rat)) index polynomial lowers uppers
      (values assignment lowers) (values assignment uppers) low high
      (by simpa [values] using hl) (by simpa [values] using hu) gl gu
      (fun i _ => by rw [values_getD, ← evaluate_rat_bridge]; rfl)
      (fun i _ => by rw [values_getD, ← evaluate_rat_bridge]; rfl) ordered
    simp only [values_getD] at step
    change _ = _ at step
    calc
      _ = _ := step
      _ = _ := ?_
    apply PolynomialSum.intervalSum_congr
    intro value
    rw [LatticeBound.update_rat_bridge]
  · rfl

/-- The involved forms and residual forms use the source's `mentions` partition. -/
def involved (index : Nat) (forms : List Linear) : List Linear := forms.filter (LatticeBound.mentions index)
def residual (index : Nat) (forms : List Linear) : List Linear := forms.filter (fun form => !(LatticeBound.mentions index form))

/-- Residual forms keep their value when the removed variable changes. -/
theorem partition_correct (assignment : Nat → Int) (index : Nat) (forms : List Linear) (value : Int) :
    holds (LatticeBound.update assignment index value) forms = true ↔
      holds assignment (residual index forms) = true ∧
      (∀ form ∈ involved index forms, 0 ≤ evaluate (LatticeBound.update assignment index value) form) := by
  simp only [holds, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro allForms
    constructor
    · intro form member
      have original := List.mem_filter.mp member
      have absent : LatticeBound.mentions index form = false := by simpa using original.2
      have same := LatticeBound.evaluate_free assignment index value form (LatticeBound.mentions_false_free index form absent)
      rw [← same]
      exact allForms form original.1
    · intro form member
      exact allForms form (List.mem_filter.mp member).1
  · rintro ⟨rest, bounds⟩ form member
    cases mentioned : LatticeBound.mentions index form with
    | false =>
      have same := LatticeBound.evaluate_free assignment index value form (LatticeBound.mentions_false_free index form mentioned)
      rw [same]
      exact rest form (List.mem_filter.mpr ⟨member, by simp [mentioned]⟩)
    | true => exact bounds form (List.mem_filter.mpr ⟨member, mentioned⟩)

/-- Finite list quantification equals indexed lookup within the valid range. -/
theorem forall_mem_getD (forms : List α) (fallback : α) (predicate : α → Prop) :
    (∀ form ∈ forms, predicate form) ↔ ∀ i, i < forms.length → predicate (forms.getD i fallback) := by
  constructor
  · intro allForms i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact allForms _ (List.getElem_mem hi)
  · intro allIndices form member
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp member
    have selected := allIndices i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, same] at selected
    exact selected

/-- The extracted bounds describe exactly all original solutions over the removed variable. -/
theorem original_interval (assignment : Nat → Int) (index : Nat) (forms lowers uppers : List Linear)
    (valid : ∀ form ∈ forms, Valid form)
    (collected : collectBounds index (involved index forms) = .ok (lowers, uppers))
    (low high : Nat) (hl : low < lowers.length) (hu : high < uppers.length)
    (gl : LatticeEliminate.lowerRegion (values assignment lowers) low = true)
    (gu : LatticeEliminate.upperRegion (values assignment uppers) high = true) (value : Int) :
    holds (LatticeBound.update assignment index value) forms = true ↔
      holds assignment (residual index forms) = true ∧
        evaluate assignment (lowers.getD low (constant 0)) ≤ value ∧
        value ≤ evaluate assignment (uppers.getD high (constant 0)) := by
  rw [partition_correct]
  have bounds := collectBounds_correct assignment index (involved index forms) lowers uppers
    (fun form member => valid form (List.mem_filter.mp member).1) collected value
  rw [bounds, forall_mem_getD lowers (constant 0), forall_mem_getD uppers (constant 0)]
  have interval := LatticeEliminate.bounds_interval (values assignment lowers) (values assignment uppers)
    low high (by simpa [values] using hl) (by simpa [values] using hu) gl gu value
  simp only [values_getD] at interval
  simp only [show (values assignment lowers).length = lowers.length by simp [values],
    show (values assignment uppers).length = uppers.length by simp [values]] at interval
  exact and_congr_right (fun _ => interval)

/-- The two failure cases emitted before region normalization. -/
inductive SplitError where
  | nonUnitCoefficient
  | unboundedVariable

/-- The raw source split, including unit checks and both finite-bound requirements. -/
def splitRaw (index : Nat) (piece : Piece) : Except SplitError (List Piece) :=
  match collectBounds index (involved index piece.constraints) with
  | .error _ => .error .nonUnitCoefficient
  | .ok (lowers, uppers) =>
    if lowers.isEmpty || uppers.isEmpty then .error .unboundedVariable
    else .ok (rawPieces index (residual index piece.constraints) lowers uppers piece.polynomial)

/-- A successful raw split supplies two nonempty lists of actual extracted bounds. -/
theorem splitRaw_success (index : Nat) (piece : Piece) (output : List Piece)
    (success : splitRaw index piece = .ok output) :
    ∃ lowers uppers, collectBounds index (involved index piece.constraints) = .ok (lowers, uppers) ∧
      0 < lowers.length ∧ 0 < uppers.length ∧
      output = rawPieces index (residual index piece.constraints) lowers uppers piece.polynomial := by
  unfold splitRaw at success
  cases found : collectBounds index (involved index piece.constraints) with
  | error error => simp [found] at success
  | ok result =>
    rcases result with ⟨lowers, uppers⟩
    simp only [found] at success
    split at success
    · cases success
    · next finite =>
      cases success
      have notEmpty : lowers.isEmpty = false ∧ uppers.isEmpty = false := by
        cases hl : lowers.isEmpty <;> cases hu : uppers.isEmpty <;> simp_all
      exact ⟨lowers, uppers, rfl,
        List.length_pos_iff.mpr (List.isEmpty_eq_false_iff.mp notEmpty.1),
        List.length_pos_iff.mpr (List.isEmpty_eq_false_iff.mp notEmpty.2), rfl⟩

/-- The successful raw caller preserves its full weighted interval and its exact support. -/
theorem splitRaw_correct (assignment : Nat → Int) (index : Nat) (piece : Piece) (output : List Piece)
    (valid : ∀ form ∈ piece.constraints, Valid form)
    (ordered : LatticePolynomial.OrderedMonomials piece.polynomial)
    (success : splitRaw index piece = .ok output) :
    ∃ low high : Int,
      (∀ value, holds (LatticeBound.update assignment index value) piece.constraints = true ↔
        holds assignment (residual index piece.constraints) = true ∧ low ≤ value ∧ value ≤ high) ∧
      (output.map (pieceValue assignment)).sum =
        if holds assignment (residual index piece.constraints) then
          Lattice.intervalSum (fun value => LatticePolynomial.evaluate
            (fun i => (LatticeBound.update assignment index value i : Rat)) piece.polynomial)
            low (high - low + 1).toNat else 0 := by
  obtain ⟨lowers, uppers, collected, lowerNonempty, upperNonempty, rfl⟩ := splitRaw_success index piece output success
  obtain ⟨low, high, hl, hu, gl, gu⟩ := LatticeEliminate.best_bounds_exist
    (values assignment lowers) (values assignment uppers)
    (by simpa [values] using lowerNonempty) (by simpa [values] using upperNonempty)
  have hl' : low < lowers.length := by simpa [values] using hl
  have hu' : high < uppers.length := by simpa [values] using hu
  refine ⟨evaluate assignment (lowers.getD low (constant 0)), evaluate assignment (uppers.getD high (constant 0)), ?_, ?_⟩
  · intro value
    exact original_interval assignment index piece.constraints lowers uppers valid collected low high hl' hu' gl gu value
  · exact rawPieces_sum assignment index (residual index piece.constraints) lowers uppers piece.polynomial low high hl' hu' gl gu ordered

/-- Defaulted lookup preserves any property of the fallback and list members. -/
theorem getD_property (forms : List α) (fallback : α) (predicate : α → Prop)
    (default : predicate fallback) (members : ∀ form ∈ forms, predicate form) (index : Nat) :
    predicate (forms.getD index fallback) := by
  induction forms generalizing index with
  | nil => exact default
  | cons form rest ih =>
    cases index with
    | zero => exact members form (by simp)
    | succ index => exact ih (fun item member => members item (by simp [member])) index

/-- Strict comparison preserves the canonical linear representation. -/
theorem strictBefore_valid (chosen current : Nat) (difference : Linear) (valid : Valid difference) :
    Valid (strictBefore chosen current difference) := by
  unfold strictBefore
  split
  · exact minus_valid difference (constant 1) valid (constant_valid 1)
  · exact valid

/-- Generated lower-comparison forms have canonical coefficient maps. -/
theorem lowerComparisons_valid (forms : List Linear) (chosen : Nat)
    (valid : ∀ form ∈ forms, Valid form) : ∀ form ∈ lowerComparisons forms chosen, Valid form := by
  intro form member
  obtain ⟨current, original, rfl⟩ := List.mem_map.mp member
  apply strictBefore_valid
  exact minus_valid _ _
    (getD_property forms (constant 0) Valid (constant_valid 0) valid chosen)
    (getD_property forms (constant 0) Valid (constant_valid 0) valid current)

/-- Generated upper-comparison forms have canonical coefficient maps. -/
theorem upperComparisons_valid (forms : List Linear) (chosen : Nat)
    (valid : ∀ form ∈ forms, Valid form) : ∀ form ∈ upperComparisons forms chosen, Valid form := by
  intro form member
  obtain ⟨current, original, rfl⟩ := List.mem_map.mp member
  apply strictBefore_valid
  exact minus_valid _ _
    (getD_property forms (constant 0) Valid (constant_valid 0) valid current)
    (getD_property forms (constant 0) Valid (constant_valid 0) valid chosen)

/-- Every generated region is a valid input to inequality normalization. -/
theorem region_valid (rest lowers uppers : List Linear) (indices : Nat × Nat)
    (hr : ∀ form ∈ rest, Valid form) (hl : ∀ form ∈ lowers, Valid form)
    (hu : ∀ form ∈ uppers, Valid form) : ∀ form ∈ region rest lowers uppers indices, Valid form := by
  intro form member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with earlier | upper
    · rcases List.mem_append.mp earlier with rest | lower
      · exact hr form rest
      · exact lowerComparisons_valid lowers indices.1 hl form lower
    · exact upperComparisons_valid uppers indices.2 hu form upper
  · obtain rfl := List.mem_singleton.mp last
    exact minus_valid _ _
      (getD_property uppers (constant 0) Valid (constant_valid 0) hu indices.2)
      (getD_property lowers (constant 0) Valid (constant_valid 0) hl indices.1)

/-- Canonical input metadata required by both region and polynomial normalization. -/
def ValidPiece (piece : Piece) : Prop :=
  (∀ form ∈ piece.constraints, Valid form) ∧ LatticePolynomial.OrderedMonomials piece.polynomial

/-- Each raw output can be passed to normalization and later elimination. -/
theorem rawPieces_valid (index : Nat) (rest lowers uppers : List Linear)
    (polynomial : LatticePolynomial.Polynomial)
    (hr : ∀ form ∈ rest, Valid form) (hl : ∀ form ∈ lowers, Valid form)
    (hu : ∀ form ∈ uppers, Valid form) :
    ∀ piece ∈ rawPieces index rest lowers uppers polynomial, ValidPiece piece := by
  intro piece member
  obtain ⟨indices, original, rfl⟩ := List.mem_map.mp member
  exact ⟨region_valid rest lowers uppers indices hr hl hu, PolynomialSum.sumOver_ordered _ _ _ _⟩

/-- Successful caller execution supplies valid metadata for every output piece. -/
theorem splitRaw_valid (index : Nat) (piece : Piece) (output : List Piece)
    (valid : ValidPiece piece) (success : splitRaw index piece = .ok output) :
    ∀ result ∈ output, ValidPiece result := by
  obtain ⟨lowers, uppers, collected, _, _, rfl⟩ := splitRaw_success index piece output success
  have metadata := collectBounds_metadata index (involved index piece.constraints) lowers uppers
    (fun form member => valid.1 form (List.mem_filter.mp member).1) collected
  exact rawPieces_valid index (residual index piece.constraints) lowers uppers piece.polynomial
    (fun form member => valid.1 form (List.mem_filter.mp member).1)
    (fun form member => (metadata.1 form member).1)
    (fun form member => (metadata.2 form member).1)

end MicroCFTA.LatticePiece
