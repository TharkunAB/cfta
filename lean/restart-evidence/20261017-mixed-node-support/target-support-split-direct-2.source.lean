import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Actual physical checks at completed inner returns

Each split retains the checks from the same supplied physical trace.
No initial capacity or independently constructed execution is required.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {A B : Type} {width fuel extra : Nat}
variable {control middle final : Control A} {before current after : Checked width}

/-- A literal prefix selects its own input checks from the full physical trace. -/
theorem split (actual : Steps fuel control before middle current)
    (trace : Trace (fuel + extra) control before final after) :
    Trace fuel control before middle current ∧ Trace extra middle current final after := by
  induction actual with
  | refl => exact ⟨.refl _ _, trace⟩
  | cons start state next reached rest result count one tail ih =>
      rw [Nat.succ_add] at trace
      cases trace with
      | cons _ _ chosen returned _ _ _ inputs step later =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (step.symm.trans one)
          have pair := ih later
          exact ⟨.cons _ _ _ _ _ _ _ inputs one pair.1, pair.2⟩

private theorem unbound_inputs (control : Control A) (next : A → Code Symbol Guard B) (state : Checked width)
    (inputs : Inputs (control.bind next) state) : Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- Removing a continuation retains each earlier literal input check. -/
theorem unbind (actual : Steps fuel control before middle current) (next : A → Code Symbol Guard B)
    (trace : Trace fuel (control.bind next) before (middle.bind next) current) :
    Trace fuel control before middle current := by
  induction actual with
  | refl => exact .refl _ _
  | cons start state resume reached rest result count one tail ih =>
      cases trace with
      | cons _ _ chosen returned _ _ _ inputs step later =>
          have bound : SourceEqualityNativeDemand.step (start.bind next) state = .yielded (resume.bind next) reached := by
            rw [step_bind, one]
            rfl
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (step.symm.trans bound)
          exact .cons _ _ _ _ _ _ _ (unbound_inputs start next state inputs) one (ih later)

/-- A completed bind derives both physical traces and their exact common checked state. -/
theorem bind_split (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (value : B) (trace : Trace fuel (control.bind next) before (.code (.pure value)) after) :
    ∃ inner outer result current, inner + outer = fuel ∧
      Trace inner control before (.code (.pure result)) current ∧
      Trace outer (.code (next result)) current (.code (.pure value)) after := by
  obtain ⟨inner, outer, result, current, count, body, _⟩ := steps_bind_inverse fuel control next before after value trace.steps
  have bound := body.bind inner control (.code (.pure result)) before current next
  have separated := split bound (count ▸ trace)
  exact ⟨inner, outer, result, current, count, unbind body next separated.1, separated.2⟩

end MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
