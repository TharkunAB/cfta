import MicroCFTA.LatticeSingleton
import MicroCFTA.PublicResult

/-!
# Complete integer candidates between the decoded endpoints

The source candidate oracle enumerates every integer between rank zero and
the last rank. The domain can have gaps. Polynomial rank order proves that
this interval contains every solution; later witness checks remove its gaps.
-/
namespace MicroCFTA.IntegerCandidateEnvelope
open LatticeSelect LatticeInput LatticeLevels LatticeCount

/-- A one-coordinate source rank is exactly the cumulative count below that coordinate. -/
theorem one_rank (levels : List (List LatticePiece.Piece)) (value : Int) (rank : Nat)
    (ranked : rankFrom levels 1 0 (fun _ => 0) [value] = some rank) :
    rank = naturalCount (cumulative levels 0 (fun _ => 0) (value - 1)) := by
  change ((if total (levels.getD 1 []) (LatticeBound.update (fun _ => 0) 0 value) = 1 then some 0 else none).bind
    (fun residual => some (naturalCount (cumulative levels 0 (fun _ => 0) (value - 1)) + residual))) = some rank at ranked
  by_cases accepted : total (levels.getD 1 []) (LatticeBound.update (fun _ => 0) 0 value) = 1
  · simpa only [accepted, ↓reduceIte, Option.bind_some, Nat.add_zero, Option.some.injEq] using ranked.symm
  · simp only [accepted, ↓reduceIte, Option.bind_none] at ranked
    cases ranked

/-- Actual polynomial cumulative ranks preserve coordinate order after successful compilation. -/
theorem core_rank_monotone (name : CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (variableOf [name]) true formula = .ok compiled)
    (levels : List (List LatticePiece.Piece))
    (built : buildLevels 1 (initial compiled) (initial_valid compiled) = .ok levels)
    (left right : Int) (leftRank rightRank : Nat) (ordered : left ≤ right)
    (leftRanked : rankFrom levels 1 0 (fun _ => 0) [left] = some leftRank)
    (rightRanked : rankFrom levels 1 0 (fun _ => 0) [right] = some rightRank) : leftRank ≤ rightRank := by
  obtain ⟨table, _, _, through, _⟩ :=
    compiled_coordinate_table [name] formula compiled parsed levels built 0 (by simp) (fun _ => 0)
  rw [one_rank levels left leftRank leftRanked, one_rank levels right rightRank rightRanked,
    ← through, ← through]
  simpa [naturalCount] using LatticeRank.through_monotone id table (left - 1) (right - 1) (by omega)

/-- Distinct increasing one-variable decoder ranks have strictly increasing integer values. -/
theorem one_decode_strict (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (left right : Fin (pointCount result.levels)) (ordered : left.val < right.val)
    (leftValue rightValue : Int)
    (leftDecoded : decode result.dimension result.levels left = [leftValue])
    (rightDecoded : decode result.dimension result.levels right = [rightValue]) : leftValue < rightValue := by
  obtain ⟨compiled, parsed, built, dimension, _⟩ :=
    LatticeAPI.points_success [name] (FullSyntax.lowerFormula formula) result success
  obtain ⟨core, _, coreParsed⟩ := FullSyntax.signed_success_is_core _ true formula compiled parsed
  have leftRanked := (decode_defined [name] core compiled coreParsed result.levels built left).2
  have rightRanked := (decode_defined [name] core compiled coreParsed result.levels built right).2
  rw [← dimension, leftDecoded] at leftRanked
  rw [← dimension, rightDecoded] at rightRanked
  have dimensionOne : result.dimension = 1 := by simpa using dimension
  rw [dimensionOne] at leftRanked rightRanked
  apply Classical.byContradiction
  intro negative
  have wrong : rightValue ≤ leftValue := by omega
  have ranks := core_rank_monotone name core compiled coreParsed result.levels built
    rightValue leftValue right.val left.val wrong rightRanked leftRanked
  omega

/-- Read the one integer produced by a valid rank. The default is unreachable after successful compilation. -/
def integerAt (result : LatticeAPI.Points) (rank : Fin (pointCount result.levels)) : Int :=
  (decode result.dimension result.levels rank).headD 0

/-- Every valid rank has exactly the singleton shape used by the source endpoint reader. -/
theorem integerAt_shape (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (rank : Fin (pointCount result.levels)) :
    decode result.dimension result.levels rank = [integerAt result rank] := by
  have exact := points_api_exact [name] formula result success
  have admitted := (exact.2.2.1 _).mpr ⟨rank, rfl⟩
  obtain ⟨value, shape⟩ := LatticeSingleton.singleton_shape _ admitted.1
  simp only [integerAt, shape, List.headD_cons]

/-- The endpoint reader is strictly increasing on the entire actual finite rank interval. -/
theorem integerAt_strict (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (left right : Fin (pointCount result.levels)) (ordered : left.val < right.val) :
    integerAt result left < integerAt result right :=
  one_decode_strict name formula result success left right ordered _ _
    (integerAt_shape name formula result success left) (integerAt_shape name formula result success right)

/-- Source interval enumeration uses an inclusive upper endpoint. -/
def interval (low high : Int) : List Int :=
  (List.range (high - low + 1).toNat).map (fun offset : Nat => low + (offset : Int))

/-- The interval includes exactly the integers between its endpoints, including gaps in the domain. -/
theorem interval_exact (low high value : Int) : value ∈ interval low high ↔ low ≤ value ∧ value ≤ high := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, bounded, rfl⟩
    omega
  · intro bounds
    refine ⟨(value - low).toNat, by omega, by omega⟩

/-- Execute the source endpoint envelope after a successful point table has been obtained. -/
def candidates (result : LatticeAPI.Points) : List Int :=
  if positive : 0 < pointCount result.levels then
    interval (integerAt result ⟨0, positive⟩)
      (integerAt result ⟨pointCount result.levels - 1, by omega⟩)
  else []

/-- Every mathematically valid integer is retained by the actual least-to-greatest candidate oracle. -/
theorem candidates_complete (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (value : Int) (valid : LatticeSingleton.Admits name formula value) : value ∈ candidates result := by
  have exact := points_api_exact [name] formula result success
  obtain ⟨rank, decoded⟩ := (exact.2.2.1 [value]).mp ⟨rfl, valid⟩
  have positive : 0 < pointCount result.levels := by have := rank.isLt; omega
  have valueAt : integerAt result rank = value := by simp [integerAt, decoded]
  simp only [candidates, positive, ↓reduceDIte, interval_exact]
  constructor
  · by_cases zero : rank.val = 0
    · have same : (⟨0, positive⟩ : Fin (pointCount result.levels)) = rank := Fin.ext zero.symm
      simp [same, valueAt]
    · have before := integerAt_strict name formula result success ⟨0, positive⟩ rank (by change 0 < rank.val; omega)
      rw [valueAt] at before
      omega
  · let last : Fin (pointCount result.levels) := ⟨pointCount result.levels - 1, by omega⟩
    by_cases finalRank : rank = last
    · change value ≤ integerAt result last
      rw [← finalRank, valueAt]
      exact Int.le_refl value
    · have before := integerAt_strict name formula result success rank last (by
        have bound := rank.isLt
        have different : rank.val ≠ last.val := fun same => finalRank (Fin.ext same)
        simp only [last] at different ⊢
        omega)
      rw [valueAt] at before
      exact Int.le_of_lt before

/-- Exact complete-term witness checks remove every gap without losing a valid integer. -/
theorem filtered_exact (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (check : Int → Bool) (correct : ∀ value, check value = true ↔ LatticeSingleton.Admits name formula value)
    (value : Int) : value ∈ (candidates result).filter check ↔ LatticeSingleton.Admits name formula value := by
  simp only [List.mem_filter, correct]
  exact ⟨And.right, fun accepted => ⟨candidates_complete name formula result success value accepted, accepted⟩⟩

/-- The source integer zero test agrees with the proved natural rank count. -/
theorem zero_count (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result) :
    pointCount result.levels = 0 ↔ result.count = 0 := by
  have count := (points_api_exact [name] formula result success).1
  have nonnegative := (LatticeAPI.points_count [name] (FullSyntax.lowerFormula formula) result success).2
  omega

/-- Preserve lattice failures before building the source integer candidate interval. -/
def integerCandidates (name : FullSyntax.Name) (formula : FullSyntax.Formula) :
    Except (LatticeAPI.Error FullSyntax.Name) (List Int) :=
  (LatticeAPI.points [name] (FullSyntax.lowerFormula formula)).map candidates

/-- An unsupported or unbounded integer domain does not become a successful empty candidate list. -/
theorem integerCandidates_error (name : FullSyntax.Name) (formula : FullSyntax.Formula)
    (error : LatticeAPI.Error FullSyntax.Name)
    (failed : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .error error) :
    integerCandidates name formula = .error error := by
  simp [integerCandidates, failed, Except.map]

end MicroCFTA.IntegerCandidateEnvelope
