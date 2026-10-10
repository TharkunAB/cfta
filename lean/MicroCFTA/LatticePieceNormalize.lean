import MicroCFTA.LatticePiece
import MicroCFTA.LatticeNormalize

/-!
# Normalization of generated polynomial pieces

Inequality normalization preserves each retained piece's contribution.
Rejected conjunctions contribute zero at every integer assignment.
-/

namespace MicroCFTA.LatticePieceNormalize

open LatticeLinear LatticePiece

/-- The Boolean conjunction agrees with the normalization specification. -/
theorem holds_iff (assignment : Nat → Int) (forms : List Linear) :
    holds assignment forms = true ↔ LatticeNormalize.Satisfies forms assignment := by
  simp [holds, LatticeNormalize.Satisfies, List.all_eq_true]

/-- Successful normalization preserves the exact Boolean region. -/
theorem normalize_holds (assignment : Nat → Int) (forms result : List Linear)
    (valid : ∀ form ∈ forms, Valid form)
    (success : LatticeNormalize.normalize forms = some result) :
    holds assignment forms = holds assignment result := by
  apply Bool.eq_iff_iff.mpr
  rw [holds_iff, holds_iff, LatticeNormalize.normalize_correct forms valid assignment]
  constructor
  · rintro ⟨other, found, satisfies⟩
    rw [success] at found
    cases found
    exact satisfies
  · intro satisfies
    exact ⟨result, success, satisfies⟩

/-- Normalize one conjunction while retaining its polynomial. -/
def normalizePiece (piece : Piece) : Option Piece :=
  (LatticeNormalize.normalize piece.constraints).map fun forms => ⟨forms, piece.polynomial⟩

/-- Normalize every raw region and omit impossible conjunctions. -/
def normalizePieces (pieces : List Piece) : List Piece := pieces.filterMap normalizePiece

/-- A conjunction rejected by normalization has zero contribution. -/
theorem rejected_value (assignment : Nat → Int) (piece : Piece) (valid : ValidPiece piece)
    (failure : LatticeNormalize.normalize piece.constraints = none) : pieceValue assignment piece = 0 := by
  unfold pieceValue
  have rejected : holds assignment piece.constraints ≠ true := by
    intro satisfies
    exact LatticeNormalize.normalize_none piece.constraints valid.1 failure assignment
      ((holds_iff assignment piece.constraints).mp satisfies)
  simp [rejected]

/-- A retained normalized region has exactly its original contribution. -/
theorem retained_value (assignment : Nat → Int) (piece : Piece) (forms : List Linear)
    (valid : ValidPiece piece) (success : LatticeNormalize.normalize piece.constraints = some forms) :
    pieceValue assignment ⟨forms, piece.polynomial⟩ = pieceValue assignment piece := by
  unfold pieceValue
  rw [normalize_holds assignment piece.constraints forms valid.1 success]

/-- Executable normalization and omission preserve the total piece weight. -/
theorem normalizePieces_value (assignment : Nat → Int) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ((normalizePieces pieces).map (pieceValue assignment)).sum = (pieces.map (pieceValue assignment)).sum := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    have head := valid piece (by simp)
    have tail : ∀ item ∈ rest, ValidPiece item := fun item member => valid item (by simp [member])
    have tailValue := ih tail
    unfold normalizePieces at tailValue
    cases found : LatticeNormalize.normalize piece.constraints with
    | none =>
      simp only [normalizePieces, List.filterMap_cons, normalizePiece, found, Option.map_none]
      rw [tailValue, List.map_cons, List.sum_cons, rejected_value assignment piece head found, Rat.zero_add]
    | some forms =>
      simp only [normalizePieces, List.filterMap_cons, normalizePiece, found, Option.map_some,
        List.map_cons, List.sum_cons]
      rw [tailValue, retained_value assignment piece forms head found]

/-- Every retained normalized piece is valid for the next elimination step. -/
theorem normalizePieces_valid (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    ∀ piece ∈ normalizePieces pieces, ValidPiece piece := by
  intro piece member
  obtain ⟨original, present, success⟩ := List.mem_filterMap.mp member
  have originalValid := valid original present
  unfold normalizePiece at success
  cases found : LatticeNormalize.normalize original.constraints with
  | none => simp [found] at success
  | some forms =>
    simp only [found, Option.map_some, Option.some.injEq] at success
    cases success
    exact ⟨LatticeNormalize.normalize_valid original.constraints originalValid.1 forms found, originalValid.2⟩

/-- The caller's raw split followed by exact region normalization. -/
def splitNormalized (index : Nat) (piece : Piece) : Except SplitError (List Piece) :=
  normalizePieces <$> splitRaw index piece

/-- Normalizing a successful raw split preserves its already proved weighted result. -/
theorem splitNormalized_value (assignment : Nat → Int) (index : Nat) (piece : Piece) (raw : List Piece)
    (valid : ValidPiece piece) (success : splitRaw index piece = .ok raw) :
    ((normalizePieces raw).map (pieceValue assignment)).sum = (raw.map (pieceValue assignment)).sum :=
  normalizePieces_value assignment raw (splitRaw_valid index piece raw valid success)

end MicroCFTA.LatticePieceNormalize
