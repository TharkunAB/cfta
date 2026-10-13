import MicroCFTA.SourceSizedDecidedTable

/-!
# Finite execution of the bounded size table

These traces count completed class calls and size passes. Their class traces
include the finite solver calls. Unknown is a completed error result.
-/

namespace MicroCFTA.SourceSizedDecidedExecution

open SourceSizedDecidedTable

/-- Execute states in order. Every call reads the same smaller-size table. -/
inductive StatesRun [DecidableEq State]
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (smaller : Table State Value) (size : Nat) :
    List State → Table State Value → Except Error (Table State Value) → Nat → Prop where
  | nil : StatesRun classRun smaller size [] built (.ok built) 0
  | error : classRun smaller size state (.error error) work →
      StatesRun classRun smaller size (state :: rest) built (.error error) (work + 1)
  | ok : classRun smaller size state (.ok terms) work →
      StatesRun classRun smaller size rest (insert built state size terms) result tailWork →
      StatesRun classRun smaller size (state :: rest) built result (work + tailWork + 1)

/-- Execute all earlier sizes before the next state pass. -/
inductive SizesRun [DecidableEq State]
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (states : List State) : Nat → Except Error (Table State Value) → Nat → Prop where
  | zero : SizesRun classRun states 0 (.ok (fun _ _ => [])) 0
  | error : SizesRun classRun states bound (.error error) work →
      SizesRun classRun states (bound + 1) (.error error) (work + 1)
  | next : SizesRun classRun states bound (.ok smaller) work →
      StatesRun classRun smaller (bound + 1) states smaller result nextWork →
      SizesRun classRun states (bound + 1) result (work + nextWork + 1)

/-- Finite class calls give a finite state fold, even when a class is empty. -/
theorem states_finite [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (completed : ∀ smaller size state, ∃ work,
      classRun smaller size state (make smaller size state) work)
    (smaller : Table State Value) (size : Nat) (states : List State)
    (built : Table State Value) :
    ∃ work, StatesRun classRun smaller size states built
      (addStates make smaller size states built) work := by
  induction states generalizing built with
  | nil => exact ⟨0, .nil⟩
  | cons state rest ih =>
      obtain ⟨work, finished⟩ := completed smaller size state
      cases result : make smaller size state with
      | error error =>
          rw [result] at finished
          exact ⟨work + 1, by
            simpa [addStates, result] using StatesRun.error (rest := rest) (built := built) finished⟩
      | ok terms =>
          rw [result] at finished
          obtain ⟨tailWork, tail⟩ := ih (insert built state size terms)
          exact ⟨work + tailWork + 1, by
            simpa [addStates, result] using StatesRun.ok finished tail⟩

/-- Every finite bound finishes under the class-call completion contract. -/
theorem sizes_finite [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (completed : ∀ smaller size state, ∃ work,
      classRun smaller size state (make smaller size state) work)
    (states : List State) (bound : Nat) :
    ∃ work, SizesRun classRun states bound (upTo make states bound) work := by
  induction bound with
  | zero => exact ⟨0, .zero⟩
  | succ bound ih =>
      obtain ⟨work, finished⟩ := ih
      cases previous : upTo make states bound with
      | error error =>
          rw [previous] at finished
          exact ⟨work + 1, by simpa [upTo, previous] using SizesRun.error finished⟩
      | ok smaller =>
          rw [previous] at finished
          obtain ⟨nextWork, next⟩ := states_finite make classRun completed
            smaller (bound + 1) states smaller
          exact ⟨work + nextWork + 1, by
            simpa [upTo, previous] using SizesRun.next finished next⟩

/-- Class-result correspondence lifts to the whole ordered state pass. -/
theorem states_result [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (agrees : ∀ smaller size state result work,
      classRun smaller size state result work → make smaller size state = result)
    {smaller size states built result work}
    (run : StatesRun classRun smaller size states built result work) :
    addStates make smaller size states built = result := by
  induction run with
  | nil => rfl
  | error finished => simp [addStates, agrees _ _ _ _ _ finished]
  | ok finished tail ih => simpa [addStates, agrees _ _ _ _ _ finished] using ih

/-- Class-result correspondence lifts to the complete finite table. -/
theorem sizes_result [DecidableEq State]
    (make : Table State Value → Nat → State → Except Error (List Value))
    (classRun : Table State Value → Nat → State → Except Error (List Value) → Nat → Prop)
    (agrees : ∀ smaller size state result work,
      classRun smaller size state result work → make smaller size state = result)
    {states bound result work} (run : SizesRun classRun states bound result work) :
    upTo make states bound = result := by
  induction run with
  | zero => rfl
  | error prior ih => simp [upTo, ih]
  | next prior next ih =>
      simpa [upTo, ih] using states_result make classRun agrees next

end MicroCFTA.SourceSizedDecidedExecution
