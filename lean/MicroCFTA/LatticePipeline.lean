import MicroCFTA.LatticePieceNormalize
import MicroCFTA.LatticeFeasible

/-!
# Metadata and weighted semantics across piece elimination

These proofs connect raw splitting to normalization and retain the variable
support needed by later elimination steps.
-/

namespace MicroCFTA.LatticePipeline

open LatticeLinear LatticePiece LatticePieceNormalize

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- A piece has no occurrence of the selected variable in its constraints or weight. -/
def FreePiece (index : Nat) (piece : Piece) : Prop :=
  (∀ form ∈ piece.constraints, PolynomialSupport.LinearFree index form) ∧
    PolynomialSupport.Free index piece.polynomial

/-- Constant linear forms contain no variables. -/
theorem constant_free (index : Nat) (value : Int) : PolynomialSupport.LinearFree index (constant value) := by
  simp [PolynomialSupport.LinearFree, constant]

/-- Sparse linear addition preserves an absent variable. -/
theorem plus_free (index : Nat) (left right : Linear)
    (hl : PolynomialSupport.LinearFree index left) (hr : PolynomialSupport.LinearFree index right) :
    PolynomialSupport.LinearFree index (plus left right) := by
  intro entry member
  have original := (List.mem_filter.mp member).1
  rcases Sparse.addSparse_sizes left.coefficients right.coefficients entry original with fromLeft | fromRight
  · obtain ⟨item, present, same⟩ := fromLeft
    rw [← same]
    exact hl item present
  · obtain ⟨item, present, same⟩ := fromRight
    rw [← same]
    exact hr item present

/-- Linear subtraction preserves an absent variable. -/
theorem minus_free (index : Nat) (left right : Linear)
    (hl : PolynomialSupport.LinearFree index left) (hr : PolynomialSupport.LinearFree index right) :
    PolynomialSupport.LinearFree index (minus left right) :=
  plus_free index left (scale (-1) right) hl (LatticeBound.scale_free index (-1) right hr)

/-- Deleting one coefficient preserves variables already absent. -/
theorem delete_preserves_free (index removed : Nat) (linear : Linear)
    (free : PolynomialSupport.LinearFree index linear) :
    PolynomialSupport.LinearFree index (LatticeBound.deleteVariable removed linear) := by
  intro entry member
  exact free entry (List.mem_filter.mp member).1

/-- Unit-bound extraction preserves each previously absent variable. -/
theorem bound_preserves_free (index removed : Nat) (linear : Linear) (result : Sum Linear Linear)
    (free : PolynomialSupport.LinearFree index linear)
    (success : LatticeBound.bound removed linear = .ok result) :
    match result with
    | .inl lower => PolynomialSupport.LinearFree index lower
    | .inr upper => PolynomialSupport.LinearFree index upper := by
  unfold LatticeBound.bound at success
  split at success
  · cases success
    exact LatticeBound.scale_free index (-1) _ (delete_preserves_free index removed linear free)
  · split at success
    · cases success; exact delete_preserves_free index removed linear free
    · cases success

/-- Traversing source constraints retains every absent variable in both bound lists. -/
theorem collectBounds_preserves_free (index removed : Nat) (forms lowers uppers : List Linear)
    (free : ∀ form ∈ forms, PolynomialSupport.LinearFree index form)
    (success : collectBounds removed forms = .ok (lowers, uppers)) :
    (∀ lower ∈ lowers, PolynomialSupport.LinearFree index lower) ∧
    (∀ upper ∈ uppers, PolynomialSupport.LinearFree index upper) := by
  induction forms generalizing lowers uppers with
  | nil =>
    simp only [collectBounds] at success
    cases success
    simp
  | cons form rest ih =>
    have headFree := free form (by simp)
    have tailFree : ∀ item ∈ rest, PolynomialSupport.LinearFree index item := fun item member => free item (by simp [member])
    cases first : LatticeBound.bound removed form with
    | error error => simp [collectBounds, first] at success
    | ok firstBound =>
      cases tail : collectBounds removed rest with
      | error error => simp [collectBounds, first, tail] at success
      | ok bounds =>
        rcases bounds with ⟨ls, us⟩
        have headMetadata := bound_preserves_free index removed form firstBound headFree first
        have tailMetadata := ih ls us tailFree tail
        cases firstBound with
        | inl lower =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨by simpa using And.intro headMetadata tailMetadata.1, tailMetadata.2⟩
        | inr upper =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨tailMetadata.1, by simpa using And.intro headMetadata tailMetadata.2⟩

/-- Strict comparison changes only a constant, so it preserves variable absence. -/
theorem strictBefore_free (index chosen current : Nat) (difference : Linear)
    (free : PolynomialSupport.LinearFree index difference) :
    PolynomialSupport.LinearFree index (strictBefore chosen current difference) := by
  unfold strictBefore
  split
  · exact minus_free index difference (constant 1) free (constant_free index 1)
  · exact free

/-- Lower comparison construction preserves the variables absent from all bounds. -/
theorem lowerComparisons_free (index : Nat) (forms : List Linear) (chosen : Nat)
    (free : ∀ form ∈ forms, PolynomialSupport.LinearFree index form) :
    ∀ form ∈ lowerComparisons forms chosen, PolynomialSupport.LinearFree index form := by
  intro form member
  obtain ⟨current, original, rfl⟩ := List.mem_map.mp member
  apply strictBefore_free
  exact minus_free index _ _
    (getD_property forms (constant 0) _ (constant_free index 0) free chosen)
    (getD_property forms (constant 0) _ (constant_free index 0) free current)

/-- Upper comparison construction preserves the variables absent from all bounds. -/
theorem upperComparisons_free (index : Nat) (forms : List Linear) (chosen : Nat)
    (free : ∀ form ∈ forms, PolynomialSupport.LinearFree index form) :
    ∀ form ∈ upperComparisons forms chosen, PolynomialSupport.LinearFree index form := by
  intro form member
  obtain ⟨current, original, rfl⟩ := List.mem_map.mp member
  apply strictBefore_free
  exact minus_free index _ _
    (getD_property forms (constant 0) _ (constant_free index 0) free current)
    (getD_property forms (constant 0) _ (constant_free index 0) free chosen)

/-- Region assembly preserves the variables absent from its residual forms and bounds. -/
theorem region_free (index : Nat) (rest lowers uppers : List Linear) (indices : Nat × Nat)
    (hr : ∀ form ∈ rest, PolynomialSupport.LinearFree index form)
    (hl : ∀ form ∈ lowers, PolynomialSupport.LinearFree index form)
    (hu : ∀ form ∈ uppers, PolynomialSupport.LinearFree index form) :
    ∀ form ∈ region rest lowers uppers indices, PolynomialSupport.LinearFree index form := by
  intro form member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with earlier | upper
    · rcases List.mem_append.mp earlier with rest | lower
      · exact hr form rest
      · exact lowerComparisons_free index lowers indices.1 hl form lower
    · exact upperComparisons_free index uppers indices.2 hu form upper
  · obtain rfl := List.mem_singleton.mp last
    exact minus_free index _ _
      (getD_property uppers (constant 0) _ (constant_free index 0) hu indices.2)
      (getD_property lowers (constant 0) _ (constant_free index 0) hl indices.1)

/-- A successful raw split removes its variable from all output constraints and weights. -/
theorem splitRaw_removes (index : Nat) (piece : Piece) (output : List Piece)
    (valid : ValidPiece piece) (success : splitRaw index piece = .ok output) :
    ∀ result ∈ output, FreePiece index result := by
  obtain ⟨lowers, uppers, collected, _, _, rfl⟩ := splitRaw_success index piece output success
  have metadata := collectBounds_metadata index (involved index piece.constraints) lowers uppers
    (fun form member => valid.1 form (List.mem_filter.mp member).1) collected
  have hl : ∀ form ∈ lowers, PolynomialSupport.LinearFree index form := fun form member => (metadata.1 form member).2
  have hu : ∀ form ∈ uppers, PolynomialSupport.LinearFree index form := fun form member => (metadata.2 form member).2
  have hr : ∀ form ∈ residual index piece.constraints, PolynomialSupport.LinearFree index form := by
    intro form member
    have absent : LatticeBound.mentions index form = false := by simpa using (List.mem_filter.mp member).2
    exact LatticeBound.mentions_false_free index form absent
  intro result member
  obtain ⟨indices, original, rfl⟩ := List.mem_map.mp member
  exact ⟨region_free index _ lowers uppers indices hr hl hu,
    PolynomialSupport.sumOver_removes index _ _ piece.polynomial
      (getD_property lowers (constant 0) _ (constant_free index 0) hl indices.1)
      (getD_property uppers (constant 0) _ (constant_free index 0) hu indices.2)⟩

/-- Raw splitting preserves variables removed by earlier steps. -/
theorem splitRaw_preserves_free (index removed : Nat) (piece : Piece) (output : List Piece)
    (free : FreePiece index piece) (success : splitRaw removed piece = .ok output) :
    ∀ result ∈ output, FreePiece index result := by
  obtain ⟨lowers, uppers, collected, _, _, rfl⟩ := splitRaw_success removed piece output success
  have metadata := collectBounds_preserves_free index removed (involved removed piece.constraints) lowers uppers
    (fun form member => free.1 form (List.mem_filter.mp member).1) collected
  have hr : ∀ form ∈ residual removed piece.constraints, PolynomialSupport.LinearFree index form :=
    fun form member => free.1 form (List.mem_filter.mp member).1
  intro result member
  obtain ⟨indices, original, rfl⟩ := List.mem_map.mp member
  exact ⟨region_free index _ lowers uppers indices hr metadata.1 metadata.2,
    PolynomialSupport.sumOver_preserves_free index removed _ _ piece.polynomial
      (getD_property lowers (constant 0) _ (constant_free index 0) metadata.1 indices.1)
      (getD_property uppers (constant 0) _ (constant_free index 0) metadata.2 indices.2) free.2⟩

/-- Normalizing regions preserves all variable removals. -/
theorem normalizePieces_free (index : Nat) (pieces : List Piece)
    (free : ∀ piece ∈ pieces, FreePiece index piece) :
    ∀ piece ∈ normalizePieces pieces, FreePiece index piece := by
  intro piece member
  obtain ⟨original, present, success⟩ := List.mem_filterMap.mp member
  have originalFree := free original present
  unfold normalizePiece at success
  cases found : LatticeNormalize.normalize original.constraints with
  | none => simp [found] at success
  | some forms =>
    simp only [found, Option.map_some, Option.some.injEq] at success
    cases success
    exact ⟨LatticeNormalize.normalize_supported (fun other => other ≠ index) original.constraints originalFree.1 forms found,
      originalFree.2⟩

/-- Equality on each enumerated integer is enough to preserve an interval sum. -/
theorem intervalSum_congr_on (left right : Int → Rat) (start : Int) (count : Nat)
    (same : ∀ k, k < count → left (start + k) = right (start + k)) :
    Lattice.intervalSum left start count = Lattice.intervalSum right start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Lattice.intervalSum, Lattice.intervalSum,
      ih (fun k hk => same k (by omega)), same count (by omega)]

/-- The interval enumerator never leaves its inclusive integer bounds. -/
theorem interval_member (low high : Int) (k : Nat) (hk : k < (high - low + 1).toNat) :
    low ≤ low + k ∧ low + k ≤ high := by
  have nonnegative : 0 ≤ high - low + 1 := by omega
  have count := Int.toNat_of_nonneg nonnegative
  omega

/-- A raw split sums the original piece contributions, with the original guard evaluated at every integer. -/
theorem splitRaw_pieceValue (assignment : Nat → Int) (index : Nat) (piece : Piece) (output : List Piece)
    (valid : ValidPiece piece) (success : splitRaw index piece = .ok output) :
    ∃ low high : Int,
      (∀ value, holds (LatticeBound.update assignment index value) piece.constraints = true → low ≤ value ∧ value ≤ high) ∧
      (output.map (pieceValue assignment)).sum =
        Lattice.intervalSum (fun value => pieceValue (LatticeBound.update assignment index value) piece)
          low (high - low + 1).toNat := by
  obtain ⟨low, high, coverage, weighted⟩ := splitRaw_correct assignment index piece output valid.1 valid.2 success
  refine ⟨low, high, ?_, ?_⟩
  · intro value satisfies
    exact ((coverage value).mp satisfies).2
  · rw [weighted]
    cases restHolds : holds assignment (residual index piece.constraints) with
    | false =>
      have zero : Lattice.intervalSum (fun value => pieceValue (LatticeBound.update assignment index value) piece)
          low (high - low + 1).toNat = Lattice.intervalSum (fun _ => 0) low (high - low + 1).toNat := by
        apply intervalSum_congr_on
        intro k hk
        have absent : holds (LatticeBound.update assignment index (low + k)) piece.constraints ≠ true := by
          intro original
          have needed := ((coverage (low + k)).mp original).1
          rw [restHolds] at needed
          contradiction
        simp [pieceValue, absent]
      rw [zero]
      simp only [Bool.false_eq_true, ↓reduceIte]
      induction (high - low + 1).toNat with
      | zero => rfl
      | succ count ih => simpa only [Lattice.intervalSum, Rat.add_zero] using ih
    | true =>
      symm
      apply intervalSum_congr_on
      intro k hk
      have accepted : holds (LatticeBound.update assignment index (low + k)) piece.constraints = true :=
        (coverage (low + k)).mpr ⟨restHolds, interval_member low high k hk⟩
      simp only [pieceValue, accepted, ↓reduceIte]

/-- Reject normalized pieces only when the executable feasibility check returns false. -/
def prunePieces : (pieces : List Piece) → (∀ piece ∈ pieces, ValidPiece piece) → List Piece
  | [], _ => []
  | piece :: rest, valid =>
    if LatticeFeasible.feasible piece.constraints (valid piece (by simp)).1 then
      piece :: prunePieces rest (fun item member => valid item (by simp [member]))
    else prunePieces rest (fun item member => valid item (by simp [member]))

/-- A rejected feasibility check can remove only zero contributions. -/
theorem infeasible_value (assignment : Nat → Int) (piece : Piece) (valid : ValidPiece piece)
    (rejected : LatticeFeasible.feasible piece.constraints valid.1 = false) :
    pieceValue assignment piece = 0 := by
  have absent : holds assignment piece.constraints ≠ true := by
    intro accepted
    exact LatticeFeasible.feasible_false piece.constraints valid.1 rejected assignment
      ((holds_iff assignment piece.constraints).mp accepted)
  simp [pieceValue, absent]

/-- Actual feasibility filtering preserves the entire signed polynomial sum. -/
theorem prunePieces_value (assignment : Nat → Int) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ((prunePieces pieces valid).map (pieceValue assignment)).sum = (pieces.map (pieceValue assignment)).sum := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    unfold prunePieces
    split
    · simp only [List.map_cons, List.sum_cons, ih]
    · next rejected =>
      have failed : LatticeFeasible.feasible piece.constraints (valid piece (by simp)).1 = false := by simpa using rejected
      rw [ih, List.map_cons, List.sum_cons, infeasible_value assignment piece (valid piece (by simp)) failed, Rat.zero_add]

/-- Filtering introduces no pieces. -/
theorem prunePieces_subset (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ∀ piece ∈ prunePieces pieces valid, piece ∈ pieces := by
  induction pieces with
  | nil => simp [prunePieces]
  | cons piece rest ih =>
    unfold prunePieces
    split
    · intro item member
      rcases List.mem_cons.mp member with same | original
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons.mpr (Or.inr (ih _ item original))
    · intro item member
      exact List.mem_cons.mpr (Or.inr (ih _ item member))

/-- Normalization and feasibility filtering in the actual source order. -/
def cleanPieces (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece) : List Piece :=
  prunePieces (normalizePieces pieces) (normalizePieces_valid pieces valid)

/-- Both source region filters preserve the weighted sum exactly. -/
theorem cleanPieces_value (assignment : Nat → Int) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ((cleanPieces pieces valid).map (pieceValue assignment)).sum = (pieces.map (pieceValue assignment)).sum := by
  rw [cleanPieces, prunePieces_value, normalizePieces_value assignment pieces valid]

theorem cleanPieces_valid (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ∀ piece ∈ cleanPieces pieces valid, ValidPiece piece := by
  intro piece member
  exact normalizePieces_valid pieces valid piece (prunePieces_subset _ _ piece member)

theorem cleanPieces_free (index : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (free : ∀ piece ∈ pieces, FreePiece index piece) :
    ∀ piece ∈ cleanPieces pieces valid, FreePiece index piece := by
  intro piece member
  exact normalizePieces_free index pieces free piece (prunePieces_subset _ _ piece member)

/-- The complete source split, including normalization and feasibility filtering. -/
def splitFull (index : Nat) (piece : Piece) (valid : ValidPiece piece) : Except SplitError (List Piece) :=
  match found : splitRaw index piece with
  | .error error => .error error
  | .ok raw => .ok (cleanPieces raw (splitRaw_valid index piece raw valid found))

/-- Successful complete splitting consists of the proved raw split and actual filters. -/
theorem splitFull_success (index : Nat) (piece : Piece) (valid : ValidPiece piece) (output : List Piece)
    (success : splitFull index piece valid = .ok output) :
    ∃ raw, ∃ found : splitRaw index piece = .ok raw,
      output = cleanPieces raw (splitRaw_valid index piece raw valid found) := by
  unfold splitFull at success
  split at success
  · cases success
  · next raw found =>
    cases success
    exact ⟨raw, found, rfl⟩

/-- The complete source split preserves weighted piece semantics without filter assumptions. -/
theorem splitFull_pieceValue (assignment : Nat → Int) (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    ∃ low high : Int,
      (∀ value, holds (LatticeBound.update assignment index value) piece.constraints = true → low ≤ value ∧ value ≤ high) ∧
      (output.map (pieceValue assignment)).sum =
        Lattice.intervalSum (fun value => pieceValue (LatticeBound.update assignment index value) piece)
          low (high - low + 1).toNat := by
  obtain ⟨raw, found, rfl⟩ := splitFull_success index piece valid output success
  obtain ⟨low, high, coverage, weighted⟩ := splitRaw_pieceValue assignment index piece raw valid found
  exact ⟨low, high, coverage, (cleanPieces_value assignment raw _).trans weighted⟩

/-- A complete split emits valid pieces for the next variable. -/
theorem splitFull_valid (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    ∀ result ∈ output, ValidPiece result := by
  obtain ⟨raw, found, rfl⟩ := splitFull_success index piece valid output success
  exact cleanPieces_valid raw _

/-- The complete split removes its variable from all retained pieces. -/
theorem splitFull_removes (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    ∀ result ∈ output, FreePiece index result := by
  obtain ⟨raw, found, rfl⟩ := splitFull_success index piece valid output success
  exact cleanPieces_free index raw _ (splitRaw_removes index piece raw valid found)

/-- The complete split retains all earlier variable removals. -/
theorem splitFull_preserves_free (index removed : Nat) (piece : Piece) (valid : ValidPiece piece)
    (free : FreePiece index piece) (output : List Piece) (success : splitFull removed piece valid = .ok output) :
    ∀ result ∈ output, FreePiece index result := by
  obtain ⟨raw, found, rfl⟩ := splitFull_success removed piece valid output success
  exact cleanPieces_free index raw _ (splitRaw_preserves_free index removed piece raw free found)

end MicroCFTA.LatticePipeline
