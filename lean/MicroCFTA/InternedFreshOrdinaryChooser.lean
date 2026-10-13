import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.EnumerationWaitingMachine

/-!
# Source fold and machine bounds for the fresh ordinary chooser

The source folds over the free-reference set. Any list with the same
ordinary members gives the mathematical chooser's exact result.
The signed-word fold agrees when the selected result fits its positive range.
-/
namespace MicroCFTA.InternedFreshOrdinaryChooser
open InternedConstructorTemplates InternedFreshOrdinaryConstruction
open InternedFreshOrdinarySourceFreeNames (freeBound_congr)
open InternedBinderProtocol (Reference)

/-- The source step increases the candidate only for an ordinary reference. -/
def above (name : Reference) (candidate : Nat) : Nat :=
  match name with
  | .uninterned level => max (level + 1) candidate
  | _ => candidate

/-- The source right fold equals the selected depth and free-name bound. -/
theorem fold_exact (names : List Reference) (depth : Nat) :
    names.foldr above depth = max depth (freeBound names) := by
  induction names with
  | nil => simp [freeBound]
  | cons name rest ih =>
      cases name <;> simp only [List.foldr_cons, above, freeBound, ih]
      case uninterned level => omega
      all_goals rfl

/-- Set iteration order and duplicate references cannot change the selected level. -/
theorem set_fold_exact (depth : Value Symbol Guard) (names : List Reference)
    (members : ∀ level, .uninterned level ∈ names ↔ .uninterned level ∈ depth.free) :
    names.foldr above depth.depth = ordinaryLevel depth := by
  rw [fold_exact, freeBound_congr names depth.free members]
  rfl

/-- One source step uses signed machine addition before the maximum. -/
def aboveWord (bits : Nat) (name : Reference) (candidate : Int) : Int :=
  match name with
  | .uninterned level => max (EnumerationWaitingMachine.wordAdd bits (level : Int) 1) candidate
  | _ => candidate

/-- A bounded chosen level bounds every increment in the source fold. -/
theorem word_fold_exact (bits : Nat) (names : List Reference) (depth : Nat)
    (fits : max depth (freeBound names) < 2 ^ bits) :
    names.foldr (aboveWord bits) (depth : Int) = ((max depth (freeBound names) : Nat) : Int) := by
  induction names with
  | nil => simp [freeBound]
  | cons name rest ih =>
      cases name <;> simp only [List.foldr_cons, aboveWord, freeBound] at fits ⊢
      case uninterned level =>
        have tailFits : max depth (freeBound rest) < 2 ^ bits := by omega
        have levelFits : level + 1 < 2 ^ bits := by omega
        have exactAdd := EnumerationWaitingMachine.wordAdd_exact bits (level : Int) 1 (by omega)
          (by exact_mod_cast levelFits)
        rw [exactAdd, ih tailFits]
        have bound : max (level + 1) (max depth (freeBound rest)) = max depth (max (level + 1) (freeBound rest)) := by omega
        omega
      all_goals exact ih fits

/-- A source set enumeration computes the exact mathematical placeholder under one result bound. -/
theorem word_set_fold_exact (bits : Nat) (depth : Value Symbol Guard) (names : List Reference)
    (members : ∀ level, .uninterned level ∈ names ↔ .uninterned level ∈ depth.free)
    (fits : ordinaryLevel depth < 2 ^ bits) :
    names.foldr (aboveWord bits) (depth.depth : Int) = (ordinaryLevel depth : Int) := by
  have same := freeBound_congr names depth.free members
  have exact := word_fold_exact bits names depth.depth (by simpa only [same, ordinaryLevel] using fits)
  simpa only [same, ordinaryLevel] using exact

end MicroCFTA.InternedFreshOrdinaryChooser
