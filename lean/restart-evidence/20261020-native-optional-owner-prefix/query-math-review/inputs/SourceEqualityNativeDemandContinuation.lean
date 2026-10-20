import MicroCFTA.SourceEqualityNativeDemand

/-!
# Continuation composition for checked native demand

Actual checked steps retain an appended continuation in yielded and blocked
controls. Errors retain their exact state. A complete inner value starts
the continuation at that same state. No semantic premise is required.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Append source code to either an ordinary control or an already demanded edge body. -/
def Control.bind (control : Control A) (next : A → Code Symbol Guard B) : Control B :=
  match control with
  | .code body => .code (body.bind next)
  | .edgeBody request rest => .edgeBody request (fun value => (rest value).bind next)

/-- Appending a pure return leaves every source instruction unchanged. -/
theorem code_bind_pure (code : Code InputSymbol InputGuard A) : code.bind .pure = code := by
  induction code <;> simp only [Code.bind, *]

/-- Appending a pure return leaves both ordinary and demanded edge-body controls unchanged. -/
theorem Control.bind_pure (control : Control A) : control.bind .pure = control := by
  cases control <;> simp only [Control.bind, code_bind_pure]

/-- Successive appended continuations associate at the exact retained control. -/
theorem Control.bind_assoc (control : Control A) (first : A → Code Symbol Guard B)
    (second : B → Code Symbol Guard C) :
    (control.bind first).bind second = control.bind (fun value => (first value).bind second) := by
  cases control <;> simp only [Control.bind, Code.bind_assoc]

/-- Append source code to every observation without losing errors, controls, or effects. -/
noncomputable def appendStep [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (next : A → Code Symbol Guard B) : Outcome width A → Outcome width B
  | .yielded control after => .yielded (control.bind next) after
  | .done value after => step (.code (next value)) after
  | .failed failure after => .failed failure after
  | .constraintError message after => .constraintError message after
  | .blocked reason control after => .blocked reason (control.bind next) after

/-- The actual edge-body prefix preserves appended code before any child continuation runs. -/
theorem body_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (rest : EdgeValue Symbol Guard → Code Symbol Guard A)
    (next : A → Code Symbol Guard B) (state : State width) :
    body request (fun value => (rest value).bind next) state = appendStep next (body request rest state) := by
  unfold body
  split
  · simp only [sentinel, appendStep, Control.bind, Code.bind_assoc]
  · split
    · rfl
    · rfl
    · split
      · rfl
      · rfl
      · dsimp only
        split <;> simp only [sentinel, appendStep, Control.bind, Code.bind_assoc]

/-- Every actual checked native step commutes with an appended source continuation. -/
theorem step_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (next : A → Code Symbol Guard B) (state : State width) :
    step (control.bind next) state = appendStep next (step control state) := by
  cases control with
  | edgeBody request rest => exact body_bind request rest next state
  | code code =>
      cases code with
      | pure | fail | work | enter | read | finishNode | finishEdge => rfl
      | optionalBinder key body rest =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.native.machine.heap <;>
            simp only [Control.bind, Code.bind, step, SourceRecursiveIntersectionNative.step, actual, lift, appendStep]
      | node request rest =>
          cases selected : lookupNode width request state.native with
          | mk selection after =>
              cases selection with
              | direct actual =>
                  simp only [Control.bind, Code.bind, step, SourceRecursiveIntersectionNative.step,
                    selected, lift, appendStep, Code.bind_assoc]
              | memoized handle =>
                  cases demanded : demandNode handle after with
                  | mk observation final =>
                      cases observation <;> simp only [Control.bind, Code.bind, step,
                        SourceRecursiveIntersectionNative.step, selected, demanded, lift, appendStep, Code.bind_assoc]
      | edge request rest =>
          cases selected : lookupEdge width request state.native with
          | mk handle after =>
              cases demanded : demandEdge handle after with
              | mk observation final =>
                  cases observation <;> simp only [Control.bind, Code.bind, step, selected, demanded, appendStep]

end MicroCFTA.SourceEqualityNativeDemand
