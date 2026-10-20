import MicroCFTA.SourceCurrentNativeTracePrefixBind

/-!
# Exact optional instructions inside physically checked prefixes

A bound trace either reaches an optional instruction in its unbound call
or completes that call and continues at the exact returned checked state.
The first case retains the full appended continuation equation.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalPrefix
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeTracePrefixBind (bind_prefix_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B : Type} {width : Nat}

/-- An actual bound optional prefix retains its same unbound instruction or exact return split. -/
theorem bound_optional_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (pair : Nat × Nat) (body : Value Symbol Guard)
    (siteNext : Value Symbol Guard → Code Symbol Guard B)
    (actual : Trace fuel (control.bind next) before (.code (.optionalBinder pair body siteNext)) after) :
    (∃ innerNext, Trace fuel control before (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind next) ∨
    (∃ innerFuel outerFuel value middle, innerFuel + outerFuel = fuel ∧
      Trace innerFuel control before (.code (.pure value)) middle ∧
      Trace outerFuel (.code (next value)) middle (.code (.optionalBinder pair body siteNext)) after) := by
  rcases bind_prefix_cases fuel control next before after (.code (.optionalBinder pair body siteNext)) actual with
    ⟨inner, called, nonpure, same⟩ | completed
  · apply Or.inl
    cases inner with
    | edgeBody => cases same
    | code code =>
        cases code with
        | pure value => exact False.elim (nonpure value rfl)
        | optionalBinder own stored innerNext =>
            change Control.code (.optionalBinder pair body siteNext) =
              .code (.optionalBinder own stored (fun value => (innerNext value).bind next)) at same
            obtain ⟨rfl, rfl, rfl⟩ := Code.optionalBinder.inj (Control.code.inj same)
            exact ⟨innerNext, called, rfl⟩
        | _ => cases same
  · exact Or.inr completed

end MicroCFTA.SourceCurrentNativeOptionalPrefix
