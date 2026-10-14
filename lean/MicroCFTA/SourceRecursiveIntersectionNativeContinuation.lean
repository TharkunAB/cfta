import MicroCFTA.SourceRecursiveIntersectionNativeRequests

/-!
# Native continuation composition

One native step commutes with appending an outer continuation. Yielded and
blocked code retains that continuation. A complete inner value starts the
outer code in the same exact state. No cache or completed body contract is
supplied for this operational law.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Append outer code to a native step without losing its control or effects. -/
def appendStep [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (next : A → Code Symbol Guard B) (outcome : Outcome width Symbol Guard A) : Outcome width Symbol Guard B :=
  match outcome with
  | .yielded code after => .yielded (code.bind next) after
  | .done value after => step emptyGuard conjoin (next value) after
  | .failed failure after => .failed failure after
  | .blocked reason code after => .blocked reason (code.bind next) after

/-- Native source steps preserve appended continuations through both recursive memo families. -/
theorem step_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    step emptyGuard conjoin (code.bind next) state = appendStep emptyGuard conjoin next (step emptyGuard conjoin code state) := by
  cases code with
  | pure value | fail failure | work job rest | enter domain left right first second rest | read name rest | finishNode handle value rest | finishEdge handle value rest => rfl
  | optionalBinder key body rest =>
    cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap <;>
      simp only [Code.bind, step, actual, appendStep]
  | node request rest =>
    cases selected : lookupNode width request state with
    | mk selection after =>
      cases selection with
      | direct actual => simp only [Code.bind, step, selected, appendStep, Code.bind_assoc]
      | memoized handle =>
        cases demanded : demandNode handle after with
        | mk observation final =>
          cases observation <;> simp only [Code.bind, step, selected, demanded, appendStep, Code.bind_assoc]
  | edge request rest =>
    cases selected : lookupEdge width request state with
    | mk handle after =>
      cases demanded : demandEdge handle after with
      | mk observation final =>
        cases observation <;> simp only [Code.bind, step, selected, demanded, appendStep, Code.bind_assoc]

end MicroCFTA.SourceRecursiveIntersectionNative
