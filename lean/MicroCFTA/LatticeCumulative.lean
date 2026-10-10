import MicroCFTA.LatticeLevels

/-!
# Cumulative completion polynomials

The source substitutes a prefix, extracts each piece's interval, and sums its
polynomial from the lower endpoint to the current variable. `through` clips
that variable at the requested bound and reads the resulting constant.
-/

namespace MicroCFTA.LatticeCumulative

open LatticePiece LatticePipeline LatticeCount LatticeLevels

local instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
local instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩

/-- One interval and the polynomial for its cumulative contribution. -/
structure CumulativePiece where
  low : Int
  high : Int
  polynomial : LatticePolynomial.Polynomial

/-- The linear upper endpoint that is the current variable itself. -/
def upTo (index : Nat) : LatticePolynomial.Linear := ⟨[(index, 1)], 0⟩

/-- The exact cumulative polynomial assembled for one successfully extracted interval. -/
def cumulativePolynomial (index : Nat) (knownValues : Nat → Option Int)
    (low : Int) (polynomial : LatticePolynomial.Polynomial) : LatticePolynomial.Polynomial :=
  PolynomialSum.sumOver index (LatticeLinear.constant low) (upTo index)
    (LatticePolynomial.substitute knownValues polynomial)

/-- The source's optional compilation of one region into a cumulative interval. -/
def cumulativePiece (index : Nat) (knownValues : Nat → Option Int) (piece : Piece) : Option CumulativePiece :=
  (LatticeInterval.intervalWithPrefix index knownValues piece.constraints).map fun (low, high) =>
    ⟨low, high, cumulativePolynomial index knownValues low piece.polynomial⟩

/-- Compile the next stored level with the specified earlier assignments. -/
def cumulativePieces (levels : List (List Piece)) (index : Nat) (knownValues : Nat → Option Int) : List CumulativePiece :=
  (levels.getD (index + 1) []).filterMap (cumulativePiece index knownValues)

/-- Assign just the current variable. -/
def singletonValue (index : Nat) (value : Int) : Nat → Option Int :=
  fun other => if other = index then some value else none

/-- The clipped constant contribution of one cumulative interval. -/
def throughPiece (index : Nat) (bound : Int) (piece : CumulativePiece) : Rat :=
  if piece.low ≤ min piece.high bound then
    LatticePolynomial.polynomialValue (LatticePolynomial.substitute (singletonValue index (min piece.high bound)) piece.polynomial)
  else 0

/-- The source's signed sum of all clipped cumulative contributions. -/
def through (index : Nat) (pieces : List CumulativePiece) (bound : Int) : Rat :=
  FiniteSum.listSum pieces (throughPiece index bound)

/-- Substitution removes an assigned variable and preserves one already absent. -/
theorem substitute_free (index : Nat) (knownValues : Nat → Option Int) (polynomial : LatticePolynomial.Polynomial)
    (free : knownValues index ≠ none ∨ PolynomialSupport.Free index polynomial) :
    PolynomialSupport.Free index (LatticePolynomial.substitute knownValues polynomial) := by
  apply PolynomialSupport.normalize_free
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  intro variableEntry variableMember
  have retained := List.mem_filter.mp variableMember
  rcases free with assigned | absent
  · intro same
    have missing : knownValues variableEntry.1 = none := by
      cases found : knownValues variableEntry.1 <;> simp_all
    rw [same] at missing
    exact assigned missing
  · exact absent original originalMember variableEntry retained.1

/-- The prefix removes earlier variables and the stored-level invariant excludes later ones. -/
theorem prefix_polynomial_free (assignment : Nat → Int) (index : Nat)
    (polynomial : LatticePolynomial.Polynomial)
    (later : ∀ other, index + 1 ≤ other → PolynomialSupport.Free other polynomial)
    (other : Nat) (apart : other ≠ index) :
    PolynomialSupport.Free other (LatticePolynomial.substitute (prefixValues assignment index) polynomial) := by
  apply substitute_free
  by_cases earlier : other < index
  · left; simp [prefixValues, earlier]
  · exact Or.inr (later other (Nat.lt_of_le_of_ne (Nat.le_of_not_gt earlier) (Ne.symm apart)))

/-- The upper endpoint has no variable other than the current one. -/
theorem upTo_free (index other : Nat) (apart : other ≠ index) : PolynomialSupport.LinearFree other (upTo index) := by
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  exact Ne.symm apart

/-- The cumulative polynomial has no variable other than the current one. -/
theorem cumulative_free (assignment : Nat → Int) (index : Nat) (low : Int)
    (polynomial : LatticePolynomial.Polynomial)
    (later : ∀ other, index + 1 ≤ other → PolynomialSupport.Free other polynomial)
    (other : Nat) (apart : other ≠ index) :
    PolynomialSupport.Free other (cumulativePolynomial index (prefixValues assignment index) low polynomial) := by
  apply PolynomialSupport.sumOver_preserves_free
  · exact LatticePipeline.constant_free other low
  · exact upTo_free index other apart
  · exact prefix_polynomial_free assignment index polynomial later other apart

/-- Substitution of the current variable agrees with its rational assignment update. -/
theorem singleton_override (assignment : Nat → Rat) (index : Nat) (value : Int) :
    LatticePolynomial.override (singletonValue index value) assignment = PolynomialSum.update assignment index (value : Rat) := by
  funext other
  by_cases same : other = index <;> simp [LatticePolynomial.override, singletonValue, PolynomialSum.update, same]

/-- If only the current variable remains, its substitution makes the constant lookup exact. -/
theorem polynomialValue_current (assignment : Nat → Rat) (index : Nat) (value : Int)
    (polynomial : LatticePolynomial.Polynomial)
    (only : ∀ other, other ≠ index → PolynomialSupport.Free other polynomial) :
    LatticePolynomial.polynomialValue (LatticePolynomial.substitute (singletonValue index value) polynomial) =
      LatticePolynomial.evaluate (PolynomialSum.update assignment index (value : Rat)) polynomial := by
  have assigned : ∀ entry ∈ polynomial, ∀ variableEntry ∈ entry.1,
      ∃ assignedValue, singletonValue index value variableEntry.1 = some assignedValue := by
    intro entry entryMember variableEntry variableMember
    by_cases current : variableEntry.1 = index
    · exact ⟨value, by simp [singletonValue, current]⟩
    · exact False.elim (only variableEntry.1 current entry entryMember variableEntry variableMember rfl)
  rw [LatticePolynomial.polynomialValue_substitute (singletonValue index value) assignment polynomial assigned,
    singleton_override]

/-- Evaluating a prefix-substituted polynomial after a current update uses the original prefix. -/
theorem prefix_override (assignment : Nat → Int) (index : Nat) (first value : Int) :
    LatticePolynomial.override (prefixValues assignment index)
      (PolynomialSum.update (PolynomialSum.update (fun other => (assignment other : Rat)) index (first : Rat)) index (value : Rat)) =
      (fun other => (LatticeBound.update assignment index value other : Rat)) := by
  funext other
  by_cases current : other = index
  · subst other; simp [LatticePolynomial.override, prefixValues, PolynomialSum.update, LatticeBound.update]
  · by_cases earlier : other < index <;>
      simp [LatticePolynomial.override, prefixValues, PolynomialSum.update, LatticeBound.update, current, earlier]

/-- The source's cumulative polynomial evaluates to an exact clipped interval sum. -/
theorem cumulative_evaluate (assignment : Nat → Int) (index : Nat) (low high : Int)
    (polynomial : LatticePolynomial.Polynomial)
    (ordered : LatticePolynomial.OrderedMonomials polynomial)
    (later : ∀ other, index + 1 ≤ other → PolynomialSupport.Free other polynomial)
    (interval : low ≤ high + 1) :
    LatticePolynomial.polynomialValue
      (LatticePolynomial.substitute (singletonValue index high)
        (cumulativePolynomial index (prefixValues assignment index) low polynomial)) =
      Lattice.intervalSum
        (fun value => LatticePolynomial.evaluate (fun other => (LatticeBound.update assignment index value other : Rat)) polynomial)
        low (high - low + 1).toNat := by
  rw [polynomialValue_current (fun other => (assignment other : Rat)) index high _
    (fun other apart => cumulative_free assignment index low polynomial later other apart)]
  unfold cumulativePolynomial
  rw [PolynomialSum.evaluate_sumOver
    (PolynomialSum.update (fun other => (assignment other : Rat)) index (high : Rat)) index
    (LatticeLinear.constant low) (upTo index) (LatticePolynomial.substitute (prefixValues assignment index) polynomial)
    low high
    (by simp [LatticePolynomial.evaluateLinear, LatticePolynomial.evaluateLinearTerms, LatticeLinear.constant, Rat.add_zero])
    (by simp [LatticePolynomial.evaluateLinear, LatticePolynomial.evaluateLinearTerms, upTo, PolynomialSum.update, Rat.zero_add, Rat.add_zero])
    interval (LatticePolynomial.substitute_ordered _ polynomial ordered)]
  apply PolynomialSum.intervalSum_congr
  intro value
  rw [LatticePolynomial.evaluate_substitute, prefix_override]

/-- Clipped cumulative evaluation sums exactly the guarded source contribution below the bound. -/
theorem throughPiece_sum (assignment : Nat → Int) (index : Nat) (bound low high : Int) (piece : Piece)
    (ordered : LatticePolynomial.OrderedMonomials piece.polynomial)
    (later : ∀ other, index + 1 ≤ other → PolynomialSupport.Free other piece.polynomial)
    (region : ∀ value, holds (LatticeBound.update assignment index value) piece.constraints = true ↔
      low ≤ value ∧ value ≤ high) :
    FiniteSum.HasSum
      (fun value => if value ≤ bound then pieceValue (LatticeBound.update assignment index value) piece else 0)
      (throughPiece index bound ⟨low, high, cumulativePolynomial index (prefixValues assignment index) low piece.polynomial⟩) := by
  let restricted := fun value => if value ≤ bound then pieceValue (LatticeBound.update assignment index value) piece else 0
  have covers : ∀ value, restricted value ≠ 0 → low ≤ value ∧ value ≤ min high bound := by
    intro value nonzero
    by_cases below : value ≤ bound
    · have admitted : holds (LatticeBound.update assignment index value) piece.constraints = true := by
        cases accepted : holds (LatticeBound.update assignment index value) piece.constraints with
        | false => simp [restricted, below, pieceValue, accepted] at nonzero
        | true => rfl
      have inside := (region value).mp admitted
      exact ⟨inside.1, by omega⟩
    · simp [restricted, below] at nonzero
  have summed := FiniteSum.of_interval restricted low (min high bound) covers
  have value : throughPiece index bound
      ⟨low, high, cumulativePolynomial index (prefixValues assignment index) low piece.polynomial⟩ =
      Lattice.intervalSum restricted low (min high bound - low + 1).toNat := by
    unfold throughPiece
    split
    · next nonempty =>
      dsimp only at nonempty
      rw [cumulative_evaluate assignment index low (min high bound) piece.polynomial ordered later (by omega)]
      apply intervalSum_congr_on
      intro k hk
      have inside := interval_member low (min high bound) k hk
      have below : low + k ≤ bound := by omega
      have admitted := (region (low + k)).mpr ⟨inside.1, by omega⟩
      simp only [restricted, below, ↓reduceIte, pieceValue, admitted]
    · next empty =>
      dsimp only at empty
      have noPoints : (min high bound - low + 1).toNat = 0 := by omega
      rw [noPoints]
      rfl
  rw [← value] at summed
  exact summed

/-- An absent optional cumulative piece contributes zero. -/
def contribution (index : Nat) (bound : Int) (piece : Option CumulativePiece) : Rat :=
  (piece.map (throughPiece index bound)).getD 0

/-- Every source piece has the exact optional cumulative contribution under a compiled level. -/
theorem cumulativePiece_sum (dimension : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (compiled : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int) (bound : Int)
    (piece : Piece) (member : piece ∈ levels.getD (index + 1) []) :
    FiniteSum.HasSum
      (fun value => if value ≤ bound then pieceValue (LatticeBound.update assignment index value) piece else 0)
      (contribution index bound (cumulativePiece index (prefixValues assignment index) piece)) := by
  unfold cumulativePiece
  cases found : LatticeInterval.intervalWithPrefix index (prefixValues assignment index) piece.constraints with
  | none =>
    have absent := buildLevels_interval_none dimension pieces valid outside levels compiled index inside assignment piece member found
    apply FiniteSum.congr FiniteSum.zero
    intro value
    by_cases below : value ≤ bound <;> simp [below, absent]
  | some endpoints =>
    rcases endpoints with ⟨low, high⟩
    exact throughPiece_sum assignment index bound low high piece
      (buildLevels_lookup_valid dimension pieces valid levels compiled (index + 1) piece member).2
      (fun other later => (buildLevels_free dimension pieces valid outside levels compiled (index + 1) (by omega)
        other later piece member).2)
      (buildLevels_interval_correct dimension pieces valid outside levels compiled index inside assignment piece member low high found)

/-- Summing an optional compilation equals summing its zero-default contributions. -/
theorem listSum_filterMap (items : List α) (compile : α → Option β) (value : β → Rat) :
    FiniteSum.listSum (items.filterMap compile) value =
      FiniteSum.listSum items (fun item => ((compile item).map value).getD 0) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases found : compile item <;> simp [FiniteSum.listSum, found, ih, Rat.zero_add]

/-- The actual source `through` computes the exact count-weighted sum below its integer bound. -/
theorem through_correct (dimension : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (compiled : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int) (bound : Int) :
    FiniteSum.HasSum
      (fun value => if value ≤ bound then total (levels.getD (index + 1) []) (LatticeBound.update assignment index value) else 0)
      (through index (cumulativePieces levels index (prefixValues assignment index)) bound) := by
  have sums := FiniteSum.listSum_hasSum (levels.getD (index + 1) [])
    (fun piece value => if value ≤ bound then pieceValue (LatticeBound.update assignment index value) piece else 0)
    (fun piece => contribution index bound (cumulativePiece index (prefixValues assignment index) piece))
    (fun piece member => cumulativePiece_sum dimension pieces valid outside levels compiled index inside assignment bound piece member)
  have assembled : through index (cumulativePieces levels index (prefixValues assignment index)) bound =
      FiniteSum.listSum (levels.getD (index + 1) [])
        (fun piece => contribution index bound (cumulativePiece index (prefixValues assignment index) piece)) := by
    exact listSum_filterMap _ _ _
  rw [← assembled] at sums
  apply FiniteSum.congr sums
  intro value
  by_cases below : value ≤ bound
  · simp only [below, ↓reduceIte, total]
  · simp only [below, ↓reduceIte, FiniteSum.listSum_zero]

/-- Source cumulative counts are natural numbers when the input has indicator-valued semantics. -/
theorem through_natural (dimension : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (natural : ∀ assignment, ∃ n : Nat, total pieces assignment = (n : Rat))
    (levels : List (List Piece)) (compiled : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int) (bound : Int) :
    ∃ n : Nat, through index (cumulativePieces levels index (prefixValues assignment index)) bound = (n : Rat) := by
  apply FiniteSum.natural (through_correct dimension pieces valid outside levels compiled index inside assignment bound)
  intro value
  by_cases below : value ≤ bound
  · simp only [below, ↓reduceIte]
    exact buildLevels_natural dimension pieces valid natural levels compiled (index + 1) (by omega)
      (LatticeBound.update assignment index value)
  · exact ⟨0, by simp [below]⟩

end MicroCFTA.LatticeCumulative
