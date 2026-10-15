import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Actual ordered native child execution

An ordered walk contains only actual child traces and their complete state
snapshots. Its length is the sum of the child trace lengths. A completed
source walk derives these child traces and outputs from actual execution.
No semantic receipt or future child answer is supplied.
-/
namespace MicroCFTA.SourceEqualityNativeDemandWalkExecution
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The ordered walk stores actual child calls and the exact state between each pair of calls. -/
inductive Walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) :
    List A → State width → List B → State width → Nat → Prop where
  | nil (state) : Walk call [] state [] state 0
  | cons (first : A) (rest) (before middle after : State width) (value values firstFuel restFuel)
      (called : Steps firstFuel (.code (call first)) before (.code (.pure value)) middle)
      (tail : Walk call rest middle values after restFuel) :
      Walk call (first :: rest) before (value :: values) after (firstFuel + restFuel)

/-- Actual child traces compose to the emitted ordered source walk with the same total length. -/
theorem Walk.trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : A → Code Symbol Guard B} {inputs : List A} {before after : State width} {values : List B} {fuel : Nat}
    (walk : Walk call inputs before values after fuel) :
    Steps fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before (.code (.pure values)) after := by
  induction walk with
  | nil state => exact .refl _ _
  | cons first rest before middle after value values firstFuel restFuel called tail ih =>
      let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind
        fun values => .pure (value :: values)
      have firstTrace := called.bind _ _ _ _ _ next
      have restTrace := ih.bind _ _ _ _ _ (fun values => .pure (value :: values))
      exact firstTrace.trans _ _ _ _ _ _ _ _ restTrace

/-- A source-walk trace derives each actual child trace and preserves the exact summed length. -/
theorem trace_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (fuel : Nat)
    (before after : State width) (values : List B)
    (trace : Steps fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before (.code (.pure values)) after) :
    Walk call inputs before values after fuel := by
  induction inputs generalizing fuel before values with
  | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace fuel [] values before after trace
      exact .nil _
  | cons first rest ih =>
      let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind
        fun values => .pure (value :: values)
      obtain ⟨firstFuel, tailFuel, value, middle, count, called, tailTrace⟩ :=
        steps_bind_inverse fuel (.code (call first)) next before after values trace
      obtain ⟨restFuel, finalFuel, restValues, current, restCount, restTrace, finalTrace⟩ :=
        steps_bind_inverse tailFuel (.code (SourceRecursiveIntersectionCode.walk call rest))
          (fun values => .pure (value :: values)) middle after values tailTrace
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace finalFuel (value :: restValues) values current after finalTrace
      have total : firstFuel + restFuel = fuel := by omega
      rw [← total]
      exact .cons first rest before middle _ value restValues firstFuel restFuel called
        (ih restFuel middle restValues restTrace)

/-- Actual completion derives an ordered child walk whose summed trace length is below the bound. -/
theorem done_walk_bounded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (fuel : Nat)
    (before after : State width) (values : List B)
    (done : execute fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before = .done values after) :
    ∃ traceFuel, traceFuel < fuel ∧ Walk call inputs before values after traceFuel := by
  obtain ⟨traceFuel, bounded, trace⟩ := done_trace fuel _ before after values done
  exact ⟨traceFuel, bounded, trace_walk call inputs traceFuel before after values trace⟩

/-- Actual completed source execution derives ordered child calls without a supplied trace plan. -/
theorem done_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (fuel : Nat)
    (before after : State width) (values : List B)
    (done : execute fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before = .done values after) :
    ∃ traceFuel, Walk call inputs before values after traceFuel := by
  obtain ⟨traceFuel, _, walk⟩ := done_walk_bounded call inputs fuel before after values done
  exact ⟨traceFuel, walk⟩

/-- Each original input has one returned child value in the ordered walk. -/
theorem Walk.length [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : A → Code Symbol Guard B} {inputs : List A} {before after : State width} {values : List B} {fuel : Nat}
    (walk : Walk call inputs before values after fuel) : values.length = inputs.length := by
  induction walk with
  | nil => rfl
  | cons first rest before middle after value values firstFuel restFuel called tail ih => exact congrArg Nat.succ ih

end MicroCFTA.SourceEqualityNativeDemandWalkExecution
