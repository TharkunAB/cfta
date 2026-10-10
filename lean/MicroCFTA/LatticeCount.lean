import MicroCFTA.LatticePipeline
import MicroCFTA.FiniteSum

/-!
# Repeated integer-variable elimination

The executable traversal splits every piece, concatenates the resulting
pieces, and repeats this operation in the supplied variable order. Every
step computes the unique finite-support sum over the removed integer variable.
-/

namespace MicroCFTA.LatticeCount

open LatticeLinear LatticePiece LatticePipeline

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- The signed polynomial contribution of all pieces at one assignment. -/
def total (pieces : List Piece) (assignment : Nat → Int) : Rat :=
  FiniteSum.listSum pieces (pieceValue assignment)

theorem total_append (left right : List Piece) (assignment : Nat → Int) :
    total (left ++ right) assignment = total left assignment + total right assignment :=
  FiniteSum.listSum_append left right (pieceValue assignment)

/-- The complete split computes a sum over all integer values, independent of interval choice. -/
theorem splitFull_sum (assignment : Nat → Int) (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    FiniteSum.HasSum (fun value => pieceValue (LatticeBound.update assignment index value) piece)
      (total output assignment) := by
  obtain ⟨low, high, covers, weighted⟩ := splitFull_pieceValue assignment index piece valid output success
  have sum := FiniteSum.of_interval
    (fun value => pieceValue (LatticeBound.update assignment index value) piece) low high
    (by
      intro value nonzero
      apply covers value
      cases accepted : holds (LatticeBound.update assignment index value) piece.constraints with
      | false => simp [pieceValue, accepted] at nonzero
      | true => rfl)
  rw [← weighted] at sum
  simpa only [total, FiniteSum.listSum_eq] using sum

/-- Traverse each source piece and concatenate the retained split pieces. -/
def eliminate (index : Nat) : (pieces : List Piece) → (∀ piece ∈ pieces, ValidPiece piece) → Except SplitError (List Piece)
  | [], _ => .ok []
  | piece :: rest, valid => do
    let first ← splitFull index piece (valid piece (by simp))
    let tail ← eliminate index rest (fun item member => valid item (by simp [member]))
    .ok (first ++ tail)

/-- Each list traversal emits valid metadata for the next variable. -/
theorem eliminate_valid (index : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : eliminate index pieces valid = .ok output) :
    ∀ piece ∈ output, ValidPiece piece := by
  induction pieces generalizing output with
  | nil => simp [eliminate] at success; cases success; simp
  | cons piece rest ih =>
    cases first : splitFull index piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate index rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        simp [eliminate, first, tail] at success
        cases success
        intro result member
        rcases List.mem_append.mp member with member | member
        · exact splitFull_valid index piece (valid piece (by simp)) head first result member
        · exact ih _ remaining tail result member

/-- Source list traversal preserves exact integer summation of the whole signed piece sum. -/
theorem eliminate_sum (assignment : Nat → Int) (index : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (output : List Piece)
    (success : eliminate index pieces valid = .ok output) :
    FiniteSum.HasSum (fun value => total pieces (LatticeBound.update assignment index value)) (total output assignment) := by
  induction pieces generalizing output with
  | nil =>
    simp [eliminate] at success
    cases success
    exact FiniteSum.zero
  | cons piece rest ih =>
    cases first : splitFull index piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate index rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        simp [eliminate, first, tail] at success
        cases success
        rw [total_append]
        exact FiniteSum.add (splitFull_sum assignment index piece (valid piece (by simp)) head first)
          (ih _ remaining tail)

/-- The whole list traversal removes its selected variable. -/
theorem eliminate_removes (index : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : eliminate index pieces valid = .ok output) :
    ∀ piece ∈ output, FreePiece index piece := by
  induction pieces generalizing output with
  | nil => simp [eliminate] at success; cases success; simp
  | cons piece rest ih =>
    cases first : splitFull index piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate index rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        simp [eliminate, first, tail] at success
        cases success
        intro result member
        rcases List.mem_append.mp member with member | member
        · exact splitFull_removes index piece (valid piece (by simp)) head first result member
        · exact ih _ remaining tail result member

/-- Traversal preserves all variables removed by earlier passes. -/
theorem eliminate_preserves_free (index removed : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (free : ∀ piece ∈ pieces, FreePiece index piece)
    (output : List Piece) (success : eliminate removed pieces valid = .ok output) :
    ∀ piece ∈ output, FreePiece index piece := by
  induction pieces generalizing output with
  | nil => simp [eliminate] at success; cases success; simp
  | cons piece rest ih =>
    cases first : splitFull removed piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate removed rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        simp [eliminate, first, tail] at success
        cases success
        intro result member
        rcases List.mem_append.mp member with member | member
        · exact splitFull_preserves_free index removed piece (valid piece (by simp)) (free piece (by simp)) head first result member
        · exact ih _ (fun item member => free item (by simp [member])) remaining tail result member

/-- Repeated finite summation in the caller's explicit variable order. -/
def SumsOut : List Nat → ((Nat → Int) → Rat) → ((Nat → Int) → Rat) → Prop
  | [], initial, result => ∀ assignment, result assignment = initial assignment
  | index :: rest, initial, result =>
    ∃ next : (Nat → Int) → Rat,
      (∀ assignment, FiniteSum.HasSum (fun value => initial (LatticeBound.update assignment index value)) (next assignment)) ∧
      SumsOut rest next result

/-- Sum each variable in sequence, stopping at the first supported-fragment error. -/
def sumOut : (order : List Nat) → (pieces : List Piece) →
    (∀ piece ∈ pieces, ValidPiece piece) → Except SplitError (List Piece)
  | [], pieces, _ => .ok pieces
  | index :: rest, pieces, valid =>
    match next : eliminate index pieces valid with
    | .error error => .error error
    | .ok output => sumOut rest output (eliminate_valid index pieces valid output next)

/-- The complete repeated caller implements exactly the iterated integer sums. -/
theorem sumOut_correct (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    SumsOut order (total pieces) (total output) := by
  induction order generalizing pieces output with
  | nil => simp [sumOut] at success; cases success; exact fun _ => rfl
  | cons index rest ih =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found =>
      exact ⟨total intermediate, fun assignment => eliminate_sum assignment index pieces valid intermediate found,
        ih intermediate _ output success⟩

/-- Every repeated output remains a canonical piece representation. -/
theorem sumOut_valid (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    ∀ piece ∈ output, ValidPiece piece := by
  induction order generalizing pieces output with
  | nil => simp [sumOut] at success; cases success; exact valid
  | cons index rest ih =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found => exact ih intermediate _ output success

/-- Repeated elimination preserves every variable already absent. -/
theorem sumOut_preserves_free (index : Nat) (order : List Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (free : ∀ piece ∈ pieces, FreePiece index piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    ∀ piece ∈ output, FreePiece index piece := by
  induction order generalizing pieces output with
  | nil => simp [sumOut] at success; cases success; exact free
  | cons removed rest ih =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found =>
      exact ih intermediate _ (eliminate_preserves_free index removed pieces valid free intermediate found) output success

/-- Every variable named in the completed order is absent from every output piece. -/
theorem sumOut_removes (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    ∀ index ∈ order, ∀ piece ∈ output, FreePiece index piece := by
  induction order generalizing pieces output with
  | nil => simp
  | cons removed rest ih =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found =>
      intro index member
      rcases List.mem_cons.mp member with same | member
      · subst index
        exact sumOut_preserves_free removed rest intermediate _
          (eliminate_removes removed pieces valid intermediate found) output success
      · exact ih intermediate _ output success index member

/-- Iterated finite summation preserves natural-valued semantics. -/
theorem sumsOut_natural (order : List Nat) (initial result : (Nat → Int) → Rat)
    (summed : SumsOut order initial result)
    (natural : ∀ assignment, ∃ n : Nat, initial assignment = (n : Rat)) :
    ∀ assignment, ∃ n : Nat, result assignment = (n : Rat) := by
  induction order generalizing initial with
  | nil => intro assignment; rw [summed assignment]; exact natural assignment
  | cons index rest ih =>
    obtain ⟨next, step, later⟩ := summed
    apply ih next later
    intro assignment
    exact FiniteSum.natural (step assignment) (fun value => natural (LatticeBound.update assignment index value))

/-- A successful elimination run cannot produce a fractional or negative total from indicator-valued input. -/
theorem sumOut_natural (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output)
    (natural : ∀ assignment, ∃ n : Nat, total pieces assignment = (n : Rat)) :
    ∀ assignment, ∃ n : Nat, total output assignment = (n : Rat) :=
  sumsOut_natural order (total pieces) (total output) (sumOut_correct order pieces valid output success) natural

/-- Terminal representation facts established by every normalized split. -/
def TerminalMetadata (piece : Piece) : Prop :=
  (∀ form ∈ piece.constraints, form.coefficients ≠ []) ∧ LatticePolynomial.UniqueMonomials piece.polynomial

/-- Every successful raw split combines duplicate polynomial keys. -/
theorem splitRaw_unique (index : Nat) (piece : Piece) (output : List Piece)
    (success : splitRaw index piece = .ok output) :
    ∀ result ∈ output, LatticePolynomial.UniqueMonomials result.polynomial := by
  obtain ⟨lowers, uppers, _, _, _, rfl⟩ := splitRaw_success index piece output success
  intro result member
  obtain ⟨indices, original, rfl⟩ := List.mem_map.mp member
  exact PolynomialSupport.sumOver_unique index _ _ piece.polynomial

/-- Complete splitting removes constant constraints and combines polynomial keys. -/
theorem splitFull_terminal (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    ∀ result ∈ output, TerminalMetadata result := by
  obtain ⟨raw, found, rfl⟩ := splitFull_success index piece valid output success
  intro result member
  have normalizedMember := prunePieces_subset _ _ result member
  obtain ⟨original, originalMember, normalizedFound⟩ := List.mem_filterMap.mp normalizedMember
  unfold LatticePieceNormalize.normalizePiece at normalizedFound
  cases normalizedEq : LatticeNormalize.normalize original.constraints with
  | none => simp [normalizedEq] at normalizedFound
  | some forms =>
    simp only [normalizedEq, Option.map_some, Option.some.injEq] at normalizedFound
    cases normalizedFound
    exact ⟨LatticeNormalize.normalize_nonconstant original.constraints forms normalizedEq,
      splitRaw_unique index piece raw found original originalMember⟩

/-- One complete pass provides terminal metadata for every output. -/
theorem eliminate_terminal (index : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : eliminate index pieces valid = .ok output) :
    ∀ piece ∈ output, TerminalMetadata piece := by
  induction pieces generalizing output with
  | nil => simp [eliminate] at success; cases success; simp
  | cons piece rest ih =>
    cases first : splitFull index piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate index rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        simp [eliminate, first, tail] at success
        cases success
        intro result member
        rcases List.mem_append.mp member with member | member
        · exact splitFull_terminal index piece (valid piece (by simp)) head first result member
        · exact ih _ remaining tail result member

/-- Repeated elimination retains metadata needed by the final `polynomialValue` read. -/
theorem sumOut_terminal (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (metadata : ∀ piece ∈ pieces, TerminalMetadata piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    ∀ piece ∈ output, TerminalMetadata piece := by
  induction order generalizing pieces output with
  | nil => simp [sumOut] at success; cases success; exact metadata
  | cons index rest ih =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found => exact ih intermediate _ (eliminate_terminal index pieces valid intermediate found) output success

/-- A nonempty elimination order establishes terminal metadata independently of the original polynomial representation. -/
theorem sumOut_nonempty_terminal (order : List Nat) (nonempty : order ≠ []) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (output : List Piece)
    (success : sumOut order pieces valid = .ok output) :
    ∀ piece ∈ output, TerminalMetadata piece := by
  cases order with
  | nil => exact False.elim (nonempty rfl)
  | cons index rest =>
    unfold sumOut at success
    split at success
    · cases success
    · next intermediate found =>
      exact sumOut_terminal rest intermediate _ (eliminate_terminal index pieces valid intermediate found) output success

/-- A linear form with no variables has an empty coefficient map. -/
theorem linearFree_all (linear : Linear) (free : ∀ index, PolynomialSupport.LinearFree index linear) :
    linear.coefficients = [] := by
  cases found : linear.coefficients with
  | nil => rfl
  | cons entry rest =>
    have impossible := free entry.1 entry (by rw [found]; simp)
    exact False.elim (impossible rfl)

/-- A retained terminal piece without variables has no remaining constraints. -/
theorem terminal_constraints_empty (piece : Piece) (metadata : TerminalMetadata piece)
    (free : ∀ index, FreePiece index piece) : piece.constraints = [] := by
  cases found : piece.constraints with
  | nil => rfl
  | cons form rest =>
    have member : form ∈ piece.constraints := by rw [found]; simp
    have empty := linearFree_all form (fun index => (free index).1 form member)
    exact False.elim (metadata.1 form member empty)

/-- After all variables are removed, the source's constant lookup equals the piece contribution. -/
theorem terminal_polynomialValue (assignment : Nat → Int) (piece : Piece) (metadata : TerminalMetadata piece)
    (free : ∀ index, FreePiece index piece) :
    LatticePolynomial.polynomialValue piece.polynomial = pieceValue assignment piece := by
  have empty := terminal_constraints_empty piece metadata free
  rw [pieceValue, empty]
  simp only [holds, List.all_nil, ↓reduceIte]
  exact PolynomialSupport.polynomialValue_free (fun index => (assignment index : Rat)) piece.polynomial
    (fun index => (free index).2) metadata.2

/-- A covering variable order removes all variables that occur in the input. -/
theorem sumOut_all_free (order : List Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (covers : ∀ index, index ∈ order ∨ ∀ piece ∈ pieces, FreePiece index piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    ∀ index, ∀ piece ∈ output, FreePiece index piece := by
  intro index
  rcases covers index with removed | absent
  · exact sumOut_removes order pieces valid output success index removed
  · exact sumOut_preserves_free index order pieces valid absent output success

/-- The final source expression adds the constant coefficients of its pieces. -/
def polynomialCount (pieces : List Piece) : Rat :=
  FiniteSum.listSum pieces (fun piece => LatticePolynomial.polynomialValue piece.polynomial)

/-- The production final count equals the complete iterated weighted sum. -/
theorem polynomialCount_correct (assignment : Nat → Int) (order : List Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (metadata : ∀ piece ∈ pieces, TerminalMetadata piece)
    (covers : ∀ index, index ∈ order ∨ ∀ piece ∈ pieces, FreePiece index piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output) :
    polynomialCount output = total output assignment := by
  apply FiniteSum.listSum_congr
  intro piece member
  exact terminal_polynomialValue assignment piece
    (sumOut_terminal order pieces valid metadata output success piece member)
    (fun index => sumOut_all_free order pieces valid covers output success index piece member)

/-- Starting from indicator-valued semantics makes the actual returned count a natural number. -/
theorem polynomialCount_natural (order : List Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (metadata : ∀ piece ∈ pieces, TerminalMetadata piece)
    (covers : ∀ index, index ∈ order ∨ ∀ piece ∈ pieces, FreePiece index piece)
    (output : List Piece) (success : sumOut order pieces valid = .ok output)
    (natural : ∀ assignment, ∃ n : Nat, total pieces assignment = (n : Rat)) :
    ∃ n : Nat, polynomialCount output = (n : Rat) := by
  rw [polynomialCount_correct (fun _ => 0) order pieces valid metadata covers output success]
  exact sumOut_natural order pieces valid output success natural (fun _ => 0)

end MicroCFTA.LatticeCount
