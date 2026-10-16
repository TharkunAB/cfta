import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning

/-!
# Actual checked semantic child trace readback

Completed physical traces determine their actual child values and states.
Splitting a continuation retains both physical traces and the exact step
count. Current initial invariants derive all reached physical effects.
No future walk or parent language law supplies the split.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {A B C : Type} {width : Nat}

/-- Earlier instructions retain their physical checks before an appended continuation. -/
theorem inputs_before_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (next : A → Code Symbol Guard B) (state : Checked width)
    (inputs : Inputs (control.bind next) state) : Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- Earlier code retains its same-cache field loads before an appended continuation. -/
theorem code_fields_before_bind (operations : SourceEqualityConstraintMemoAllocation.State)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (fields : SourceCurrentAllocatedNativeCodeFields.Fields operations (code.bind next)) :
    SourceCurrentAllocatedNativeCodeFields.Fields operations code := by
  induction code with
  | pure | fail => trivial
  | work job resume ih => exact ⟨fields.1, fun value => ih value (fields.2 value)⟩
  | enter domain left right first second resume ih | read name resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih => exact fun value => ih value (fields value)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih fields

/-- A control's allocated fields do not depend on a later appended continuation. -/
theorem fields_before_bind (control : Control A) (next : A → Code Symbol Guard B) (state : Checked width)
    (fields : Fields (control.bind next) state) : Fields control state := by
  cases control with
  | code code => exact code_fields_before_bind state.operations code next fields
  | edgeBody request resume =>
      exact ⟨fields.1, fun value => code_fields_before_bind state.operations (resume value) next (fields.2 value)⟩

/-- A completed physical trace exposes the remainder after its actual first yielded step. -/
theorem after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : Control A) (before middle after : Checked width) (value : A)
    (trace : Trace fuel control before (.code (.pure value)) after)
    (one : step control before = .yielded next middle) :
    ∃ restFuel, fuel = restFuel + 1 ∧ Trace restFuel next middle (.code (.pure value)) after := by
  cases trace with
  | refl => cases one
  | cons control before rest current final after count inputs actual tail =>
      have same := Outcome.yielded.inj (one.symm.trans actual)
      rcases same.1 with rfl
      rcases same.2 with rfl
      exact ⟨count, rfl, tail⟩

/-- A completed physical trace contains its current physical input check. -/
theorem current_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after) : Inputs control before := by
  cases trace with
  | refl => trivial
  | cons control before next middle final after count inputs one tail => exact inputs

/-- A terminal constructor derives its literal result, full state, and actual operand check. -/
theorem work_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard A) (fuel : Nat) (before after : Checked width) (value : A)
    (trace : Trace fuel (.code (.work job .pure)) before (.code (.pure value)) after) :
    fuel = 1 ∧ value = (run job before.native.machine.heap).1 ∧
      after = {before with native := advance before.native {before.native.machine with heap := (run job before.native.machine.heap).2}} ∧
      SourceEqualityNativeDemandHeapPrimitives.WorkInputs before.native.machine.heap job := by
  have inputs := current_inputs trace
  have one : step (.code (.work job .pure)) before = .yielded
      (.code (.pure (run job before.native.machine.heap).1))
      {before with native := advance before.native {before.native.machine with heap := (run job before.native.machine.heap).2}} := rfl
  obtain ⟨count, total, rest⟩ := after_step fuel _ _ before _ after value trace one
  obtain ⟨rfl, same, retained⟩ := pure_trace count _ value _ after rest.steps
  exact ⟨total, same.symm, retained.symm, inputs⟩

/-- Completed appended physical execution derives both exact physical child traces. -/
theorem bind_inverse [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (state after : Checked width) (value : B)
    (trace : Trace fuel (control.bind next) state (.code (.pure value)) after) :
    ∃ (inner outer : Nat) (result : A) (middle : Checked width), inner + outer = fuel ∧
      Trace inner control state (.code (.pure result)) middle ∧
      Trace outer (.code (next result)) middle (.code (.pure value)) after := by
  induction fuel generalizing control state with
  | zero =>
      have same := steps_zero _ _ _ _ trace.steps
      cases control with
      | edgeBody => cases same.1
      | code code =>
          cases code with
          | pure result => exact ⟨0, 0, result, state, rfl, .refl _ _, trace⟩
          | fail | work | enter | read | optionalBinder | node | edge | finishNode | finishEdge => cases same.1
  | succ fuel ih =>
      cases trace with
      | cons start before rest current final after count inputs oneBound tail =>
          have boundStep := step_bind control next state
          cases one : step control state with
          | done result initial =>
              obtain ⟨pure, retained⟩ := (step_done_iff control state initial result).mp one
              subst control
              subst initial
              exact ⟨0, fuel + 1, result, state, by omega, .refl _ _,
                .cons _ _ _ _ _ _ _ inputs oneBound tail⟩
          | yielded body middle =>
              rw [one, appendStep] at boundStep
              have same := Outcome.yielded.inj (boundStep.symm.trans oneBound)
              rcases same.1 with rfl
              rcases same.2 with rfl
              obtain ⟨inner, outer, result, final, count, bodyTrace, outerTrace⟩ := ih body middle tail
              exact ⟨inner + 1, outer, result, final, by omega,
                .cons _ _ _ _ _ _ _ (inputs_before_bind control next state inputs) one bodyTrace, outerTrace⟩
          | failed failure middle | constraintError message middle | blocked reason body middle =>
              rw [one, appendStep] at boundStep
              cases boundStep.symm.trans oneBound

private theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) : SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

/-- Initial invariants derive every reached state, history, and continuation field receipt. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (valid : Good before) (fields : Fields control before) :
    Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧ Fields rest after := by
  induction trace with
  | refl control state => exact ⟨valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
      SourceEqualityConstraintMemoAllocation.grows_refl _, fields⟩
  | cons control state next current final result count inputs one tail ih =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control state valid inputs fields
      have reached : Good current ∧ Extension state.native.machine current.native.machine ∧
          SourceEqualityRequiredCache.Keeps state.native.machine.heap current.native.machine.heap ∧
          SourceEqualityConstraintMemoAllocation.Grows state.operations current.operations ∧ Fields next current := by
        rw [one] at checked
        exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.2⟩
      have later := ih reached.1 reached.2.2.2.2
      exact ⟨later.1, reached.2.1.trans later.2.1, reached.2.2.1.trans later.2.2.1,
        operations_trans reached.2.2.2.1 later.2.2.2.1, later.2.2.2.2⟩

/-- Actual bind readback derives the child prefix and all physical continuation invariants. -/
theorem bind_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B) (before after : Checked width) (value : B)
    (trace : Trace fuel (control.bind next) before (.code (.pure value)) after)
    (valid : Good before) (fields : Fields (control.bind next) before) (ranges : WordRanges (control.bind next) before) :
    ∃ (inner outer : Nat) (result : A) (middle : Checked width), inner + outer = fuel ∧
      Trace inner control before (.code (.pure result)) middle ∧
      Trace outer (.code (next result)) middle (.code (.pure value)) after ∧
      Good middle ∧ Extension before.native.machine middle.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations ∧ Fields (.code (next result)) middle ∧
      WordRanges control before ∧ WordRanges (.code (next result)) middle := by
  obtain ⟨inner, outer, result, middle, count, first, rest⟩ := bind_inverse fuel control next before after value trace
  have reached := effects (first.bind next) valid fields
  exact ⟨inner, outer, result, middle, count, first, rest, reached.1, reached.2.1, reached.2.2.1,
    reached.2.2.2.1, reached.2.2.2.2, ranges.before_bind control next before,
    ranges.after_body control next before middle inner result first.steps⟩

/-- An ordered walk contains only the actual reached physical child prefixes. -/
inductive Walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) :
    List A → Checked width → List B → Checked width → Nat → Prop where
  | nil (state) : Walk call [] state [] state 0
  | cons (first : A) (rest) (before middle after : Checked width) (value values firstFuel restFuel)
      (called : Trace firstFuel (.code (call first)) before (.code (.pure value)) middle)
      (tail : Walk call rest middle values after restFuel) :
      Walk call (first :: rest) before (value :: values) after (firstFuel + restFuel)

/-- Actual child prefixes compose back to the same literal physical walk. -/
theorem Walk.trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : A → Code Symbol Guard B} {inputs : List A} {before after : Checked width} {values : List B} {fuel : Nat}
    (walk : Walk call inputs before values after fuel) :
    Trace fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before (.code (.pure values)) after := by
  induction walk with
  | nil state => exact .refl _ _
  | cons first rest before middle after value values firstFuel restFuel called tail ih =>
      let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind fun values => .pure (value :: values)
      exact (called.bind next).trans (ih.bind (fun values => .pure (value :: values)))

/-- Completed actual walks determine every child result and exact intermediate physical trace. -/
theorem walk_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (fuel : Nat) (before after : Checked width) (values : List B)
    (trace : Trace fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) before (.code (.pure values)) after) :
    Walk call inputs before values after fuel := by
  induction inputs generalizing fuel before values with
  | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace fuel [] values before after trace.steps
      exact .nil _
  | cons first rest ih =>
      let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind fun values => .pure (value :: values)
      obtain ⟨firstFuel, tailFuel, value, middle, count, called, tailTrace⟩ :=
        bind_inverse fuel (.code (call first)) next before after values trace
      obtain ⟨restFuel, finalFuel, restValues, current, restCount, restTrace, finalTrace⟩ :=
        bind_inverse tailFuel (.code (SourceRecursiveIntersectionCode.walk call rest))
          (fun values => .pure (value :: values)) middle after values tailTrace
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace finalFuel (value :: restValues) values current after finalTrace.steps
      have total : firstFuel + restFuel = fuel := by omega
      rw [← total]
      exact .cons first rest before middle _ value restValues firstFuel restFuel called (ih restFuel middle restValues restTrace)

/-- A nonempty actual walk derives the first result and the complete reached tail scope. -/
theorem cons_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (first : A) (rest : List A) (fuel : Nat)
    (before after : Checked width) (outputs : List B)
    (trace : Trace fuel (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before (.code (.pure outputs)) after)
    (valid : Good before) (fields : Fields (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before)
    (ranges : WordRanges (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before) :
    ∃ (firstFuel restFuel : Nat) (value : B) (values : List B) (middle : Checked width), firstFuel + restFuel = fuel ∧
      outputs = value :: values ∧ Trace firstFuel (.code (call first)) before (.code (.pure value)) middle ∧
      Trace restFuel (.code (SourceRecursiveIntersectionCode.walk call rest)) middle (.code (.pure values)) after ∧
      Good middle ∧ Extension before.native.machine middle.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations ∧
      Fields (.code (SourceRecursiveIntersectionCode.walk call rest)) middle ∧
      WordRanges (.code (call first)) before ∧ WordRanges (.code (SourceRecursiveIntersectionCode.walk call rest)) middle := by
  let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind fun values => .pure (value :: values)
  obtain ⟨firstFuel, tailFuel, value, middle, count, called, tailTrace, reached, extension, keeps, operations, tailFields, firstRanges, tailRanges⟩ :=
    bind_readback fuel (.code (call first)) next before after outputs trace valid fields ranges
  obtain ⟨restFuel, finalFuel, values, current, restCount, restTrace, finalTrace⟩ :=
    bind_inverse tailFuel (.code (SourceRecursiveIntersectionCode.walk call rest))
      (fun values => .pure (value :: values)) middle after outputs tailTrace
  obtain ⟨rfl, rfl, rfl⟩ := pure_trace finalFuel (value :: values) outputs current after finalTrace.steps
  exact ⟨firstFuel, restFuel, value, values, middle, by omega, rfl, called, restTrace, reached, extension, keeps, operations,
    fields_before_bind (.code (SourceRecursiveIntersectionCode.walk call rest)) (fun values => .pure (value :: values)) middle tailFields,
    firstRanges, tailRanges.before_bind (.code (SourceRecursiveIntersectionCode.walk call rest)) (fun values => .pure (value :: values)) middle⟩

/-- Actual ordered calls determine the final constructor's operands and full reached state. -/
theorem walk_work_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (finish : List B → Work Symbol Guard C)
    (fuel : Nat) (before after : Checked width) (value : C)
    (trace : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk call inputs).bind fun values => .work (finish values) .pure))
      before (.code (.pure value)) after)
    (valid : Good before)
    (fields : Fields (.code ((SourceRecursiveIntersectionCode.walk call inputs).bind fun values => .work (finish values) .pure)) before)
    (ranges : WordRanges (.code ((SourceRecursiveIntersectionCode.walk call inputs).bind fun values => .work (finish values) .pure)) before) :
    ∃ (walkFuel : Nat) (values : List B) (middle : Checked width), fuel = walkFuel + 1 ∧
      Walk call inputs before values middle walkFuel ∧ Good middle ∧
      Extension before.native.machine middle.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations ∧
      SourceEqualityNativeDemandHeapPrimitives.WorkInputs middle.native.machine.heap (finish values) ∧
      value = (run (finish values) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap := (run (finish values) middle.native.machine.heap).2}} ∧
      WordRanges (.code (SourceRecursiveIntersectionCode.walk call inputs)) before := by
  obtain ⟨inner, outer, values, middle, count, walked, finished, reached, extension, keeps, operations, _, walkRanges, _⟩ :=
    bind_readback fuel (.code (SourceRecursiveIntersectionCode.walk call inputs)) (fun values => .work (finish values) .pure)
      before after value trace valid fields ranges
  obtain ⟨rfl, same, retained, operands⟩ := work_readback (finish values) outer middle after value finished
  exact ⟨inner, values, middle, count.symm, walk_readback call inputs inner before middle values walked,
    reached, extension, keeps, operations, operands, same, retained, walkRanges⟩

end MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
