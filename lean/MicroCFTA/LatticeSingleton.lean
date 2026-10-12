import MicroCFTA.LatticeSelect

/-!
# Exact singleton integer queries

The source `onlyPoint` compiles one variable, requires a count of one, and
decodes rank zero. It returns a value exactly when that successfully compiled
formula has one integer solution.
-/

namespace MicroCFTA.LatticeSingleton
open LatticeInput LatticeSelect

/-- The complete one-variable interpretation used by the public point query. -/
def Admits (name : FullSyntax.Name) (formula : FullSyntax.Formula) (value : Int) : Prop :=
  FullSyntax.Holds FullSyntax.integerModel (nameValues [name] (assignTuple (fun _ => 0) 0 [value])) formula

/-- The source reads rank zero only after its integer count is exactly one. -/
def onlyPoint (name : FullSyntax.Name) (formula : FullSyntax.Formula) : Option Int :=
  match LatticeAPI.points [name] (FullSyntax.lowerFormula formula) with
  | .error _ => none
  | .ok result =>
    if result.count = 1 then
      match (decodeFrom result.levels result.dimension 0 (fun _ => 0) 0).getD [] with
      | [value] => some value
      | _ => none
    else none

/-- One-element tuple length has exactly the source's singleton list form. -/
theorem singleton_shape (values : List Int) (length : values.length = 1) : ∃ value, values = [value] := by
  cases values with
  | nil => simp at length
  | cons value rest =>
    have empty : rest = [] := List.length_eq_zero_iff.mp (by simpa using length)
    exact ⟨value, by simp [empty]⟩

/-- A returned value satisfies the formula and is its only integer solution. -/
theorem onlyPoint_sound (name : FullSyntax.Name) (formula : FullSyntax.Formula) (value : Int)
    (returned : onlyPoint name formula = some value) :
    Admits name formula value ∧ ∀ other, Admits name formula other → other = value := by
  cases compiled : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) with
  | error error => simp [onlyPoint, compiled] at returned
  | ok result =>
    by_cases one : result.count = 1
    · have exact := points_api_exact [name] formula result compiled
      have count : pointCount result.levels = 1 := by simpa [one] using exact.1.symm
      let zero : Fin (pointCount result.levels) := ⟨0, by omega⟩
      have decoded : decode result.dimension result.levels zero = [value] := by
        simp only [onlyPoint, compiled, ite_eq_left one] at returned
        cases raw : (decodeFrom result.levels result.dimension 0 (fun _ => 0) 0).getD [] with
        | nil => simp [raw] at returned
        | cons first rest =>
          cases rest with
          | cons next tail => simp [raw] at returned
          | nil =>
            have same : first = value := by simpa [raw] using returned
            simpa [decode, zero, same] using raw
      have admitted := (exact.2.2.1 [value]).mpr ⟨zero, decoded⟩
      refine ⟨admitted.2, ?_⟩
      intro other accepted
      obtain ⟨rank, rankValue⟩ := (exact.2.2.1 [other]).mp ⟨rfl, accepted⟩
      have sameRank : rank = zero := Fin.ext (by have inside := rank.isLt; simp only [zero]; omega)
      have same := decoded.symm.trans (sameRank ▸ rankValue)
      exact (List.cons.inj same).1.symm
    · simp [onlyPoint, compiled, one] at returned

/-- Every uniquely solvable successfully compiled one-variable query returns its solution. -/
theorem onlyPoint_complete (name : FullSyntax.Name) (formula : FullSyntax.Formula) (value : Int)
    (result : LatticeAPI.Points)
    (compiled : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result)
    (accepted : Admits name formula value) (unique : ∀ other, Admits name formula other → other = value) :
    onlyPoint name formula = some value := by
  have exact := points_api_exact [name] formula result compiled
  obtain ⟨witness, witnessValue⟩ := (exact.2.2.1 [value]).mp ⟨rfl, accepted⟩
  have allValues : ∀ rank : Fin (pointCount result.levels), decode result.dimension result.levels rank = [value] := by
    intro rank
    have admitted := (exact.2.2.1 _).mpr ⟨rank, rfl⟩
    obtain ⟨other, shape⟩ := singleton_shape _ admitted.1
    have accepted : Admits name formula other := by simpa [Admits, shape] using admitted.2
    simpa [unique other accepted] using shape
  have positive : 0 < pointCount result.levels := by have bound := witness.isLt; omega
  let zero : Fin (pointCount result.levels) := ⟨0, positive⟩
  have count : pointCount result.levels = 1 := by
    by_cases large : 1 < pointCount result.levels
    · let one : Fin (pointCount result.levels) := ⟨1, large⟩
      have same := exact.2.2.2 ((allValues zero).trans (allValues one).symm)
      have impossible := congrArg Fin.val same
      simp [zero, one] at impossible
    · omega
  have nonnegative := (LatticeAPI.points_count [name] (FullSyntax.lowerFormula formula) result compiled).2
  have one : result.count = 1 := by have natCount := exact.1; omega
  have decoded := allValues zero
  change (decodeFrom result.levels result.dimension 0 (fun _ => 0) 0).getD [] = [value] at decoded
  simp [onlyPoint, compiled, one, decoded]

/-- The successful source singleton API returns all and only the unique solutions. -/
theorem onlyPoint_exact (name : FullSyntax.Name) (formula : FullSyntax.Formula) (value : Int)
    (result : LatticeAPI.Points)
    (compiled : LatticeAPI.points [name] (FullSyntax.lowerFormula formula) = .ok result) :
    onlyPoint name formula = some value ↔
      Admits name formula value ∧ ∀ other, Admits name formula other → other = value :=
  ⟨onlyPoint_sound name formula value, fun ⟨accepted, unique⟩ => onlyPoint_complete name formula value result compiled accepted unique⟩

end MicroCFTA.LatticeSingleton
