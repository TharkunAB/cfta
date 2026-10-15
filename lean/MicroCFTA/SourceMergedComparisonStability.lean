import MicroCFTA.SourceMergedComparisonCompletion
import MicroCFTA.MergedComparisonStability

/-!
# Exact stability of completed general repaired comparisons

Extra comparison fuel preserves the Boolean and complete actual cache.
The proof follows repaired reads and every ordered recursive stage.
No semantic or prepared-body premise is required for completed traces.
-/
namespace MicroCFTA.SourceMergedComparisonStability
open InternedConstructorTemplates
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryExposure (read)
open MergedFreshOrdinaryComparison (check allRows)
open MergedComparisonStability (Refines bind_refines children_refines anyCover_refines)

/-- A completed physical source read retains its rows and exact cache at extra fuel. -/
theorem read_refines [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat) (value : Value Symbol Guard) :
    Refines (read fuel value) (read (fuel + extra) value) := by
  intro state edges after done
  unfold MergedFreshOrdinaryExposure.read at done ⊢
  cases original : MergedFreshOrdinaryExposure.nodeEdges fuel value state with
  | unresolved | pending | exhausted => simp only [original] at done; cases done
  | done rows final =>
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra value state (by rw [original]; trivial)
      simpa only [stable] using done

/-- Every demanded wide read and ordered cover preserves its completed result at extra fuel. -/
theorem allRows_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (fuel extra : Nat) (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (same : ∀ wide narrow, Refines (first wide narrow) (second wide narrow))
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) :
    Refines (allRows fuel clear first wide narrows) (allRows (fuel + extra) clear second wide narrows) := by
  induction narrows with
  | nil => exact .refl _
  | cons narrow rest ih =>
      exact bind_refines _ _ _ _ (read_refines fuel extra wide) (fun wides =>
        bind_refines _ _ _ _ (anyCover_refines clear first second same narrow wides)
          (fun accepted => by cases accepted with
            | false => exact .refl _
            | true => exact ih))

/-- Extra recursive fuel preserves each completed Boolean and its exact source cache. -/
theorem check_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) :
    Refines (check clear fuel above wide narrow) (check clear (fuel + extra) above wide narrow) := by
  intro state value after done
  rw [check] at done ⊢
  by_cases narrowEmpty : narrow.referenceOf = .empty
  · simpa only [narrowEmpty, ↓reduceIte] using done
  simp only [narrowEmpty, ↓reduceIte] at done ⊢
  by_cases wideEmpty : wide.referenceOf = .empty
  · simpa only [wideEmpty, ↓reduceIte] using done
  simp only [wideEmpty, ↓reduceIte] at done ⊢
  by_cases same : wide.referenceOf = narrow.referenceOf
  · simpa only [same, ↓reduceIte] using done
  simp only [same, ↓reduceIte] at done ⊢
  cases wideFound : identity wide with
  | none => simp only [wideFound] at done; cases done
  | some wideId =>
      cases narrowFound : identity narrow with
      | none => simp only [wideFound, narrowFound] at done; cases done
      | some narrowId =>
          simp only [wideFound, narrowFound] at done ⊢
          by_cases visited : (wideId, narrowId) ∈ above
          · simpa only [visited, ↓reduceIte] using done
          simp only [visited, ↓reduceIte] at done ⊢
          cases fuel with
          | zero => cases done
          | succ fuel =>
              have recursive : ∀ (left right : Value Symbol Guard),
                  Refines (check clear fuel ((wideId, narrowId) :: above) left right)
                    (check clear (fuel + extra) ((wideId, narrowId) :: above) left right) :=
                fun left right => check_refines clear fuel extra ((wideId, narrowId) :: above) left right
              simpa only [Nat.succ_add] using
                bind_refines _ _ _ _ (read_refines (fuel + 1) extra narrow)
                  (fun narrows => allRows_refines (fuel + 1) extra clear _ _ recursive wide narrows)
                  state value after done
termination_by fuel

/-- A completed comparison has the same full result at every larger fuel. -/
theorem check_stable [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (value : Bool) (after : State Symbol Guard)
    (done : check clear fuel above wide narrow state = .done value after) :
    check clear (fuel + extra) above wide narrow state = check clear fuel above wide narrow state :=
  (check_refines clear fuel extra above wide narrow state value after done).trans done.symm

/-- Any two completed fuel choices return the same Boolean and exact physical cache. -/
theorem successful_results_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (first second : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (left right : Bool) (after final : State Symbol Guard)
    (firstDone : check clear first above wide narrow state = .done left after)
    (secondDone : check clear second above wide narrow state = .done right final) :
    (left, after) = (right, final) := by
  have firstReplay := check_refines clear first second above wide narrow state left after firstDone
  have secondReplay := check_refines clear second first above wide narrow state right final secondDone
  rw [Nat.add_comm second first] at secondReplay
  have same := Result.done.inj (firstReplay.symm.trans secondReplay)
  exact Prod.ext same.1 same.2

end MicroCFTA.SourceMergedComparisonStability
