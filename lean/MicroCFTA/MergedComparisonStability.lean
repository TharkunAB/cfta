import MicroCFTA.MergedSourceComparison
import MicroCFTA.MergedColdReaderTermination

/-!
# Extra fuel preserves completed physical comparisons

Every completed comparison retains its exact Boolean and final cache when
the recursive fuel increases. The proof follows the ordered source reads,
child comparisons, and cover searches. It requires no semantic premises.
-/
namespace MicroCFTA.MergedComparisonStability
open InternedConstructorTemplates MergedSourceComparison

/-- Preserve a completed value and its exact final physical cache. -/
def Refines (first second : State Symbol Guard → Result Symbol Guard Output) : Prop :=
  ∀ state value after, first state = .done value after → second state = .done value after

/-- The same action preserves every completed result. -/
theorem Refines.refl (action : State Symbol Guard → Result Symbol Guard Output) : Refines action action :=
  fun _ _ _ done => done

/-- Ordered sequencing preserves every completed result of both actions. -/
theorem bind_refines (first second : State Symbol Guard → Result Symbol Guard First)
    (left right : First → State Symbol Guard → Result Symbol Guard Output)
    (head : Refines first second) (tail : ∀ value, Refines (left value) (right value)) :
    Refines (fun state => (first state).bind left) (fun state => (second state).bind right) := by
  intro state value after done
  cases firstDone : first state with
  | failed fault middle => simp [Result.bind, firstDone] at done
  | done result middle =>
      have tailDone : left result middle = .done value after := by
        simpa only [firstDone, Result.bind] using done
      simpa only [head state result middle firstDone, Result.bind] using
        tail result middle value after tailDone

/-- A completed physical source read retains its rows and exact cache at extra fuel. -/
theorem read_refines [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat) (value : Value Symbol Guard) :
    Refines (read fuel value) (read (fuel + extra) value) := by
  intro state edges after done
  unfold MergedSourceComparison.read at done ⊢
  cases original : MergedSourceExposure.nodeEdges fuel value state with
  | unresolved | pending | exhausted => simp only [original] at done; cases done
  | done rows final =>
      have stable := MergedColdReaderTermination.nodeEdges_stable fuel extra value state (by rw [original]; trivial)
      simpa only [stable] using done

/-- Child conjunction preserves the exact successful trace of its callback. -/
theorem children_refines
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (same : ∀ wide narrow, Refines (first wide narrow) (second wide narrow))
    (wides narrows : List (Value Symbol Guard)) :
    Refines (children first wides narrows) (children second wides narrows) := by
  induction wides generalizing narrows with
  | nil => exact .refl _
  | cons wide wides ih =>
      cases narrows with
      | nil => exact .refl _
      | cons narrow narrows =>
          exact bind_refines _ _ _ _ (same wide narrow) (fun accepted => by
            cases accepted with
            | false => exact .refl _
            | true => exact ih narrows)

/-- Ordered cover search preserves completed callback results and short-circuit caches. -/
theorem anyCover_refines [DecidableEq Symbol] (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (same : ∀ wide narrow, Refines (first wide narrow) (second wide narrow))
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) :
    Refines (anyCover clear first narrow wides) (anyCover clear second narrow wides) := by
  induction wides with
  | nil => exact .refl _
  | cons wide rest ih =>
      simp only [anyCover]
      split
      · exact bind_refines _ _ _ _ (children_refines first second same wide.children narrow.children)
          (fun accepted => by cases accepted with
            | false => exact ih
            | true => exact .refl _)
      · exact ih

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

end MicroCFTA.MergedComparisonStability
