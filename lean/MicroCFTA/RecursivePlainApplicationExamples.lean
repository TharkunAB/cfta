import MicroCFTA.RecursivePlainApplication
import MicroCFTA.RecursiveCompleteExample

/-!
# Ordinary application inside complete mutual families

This example uses the Apply constructor and plain runtime flags. Both
recursive keys retain the same compiler for every complete record field.
-/
namespace MicroCFTA.RecursivePlainApplicationExamples
open RecursivePlainApplication
open RecursiveNaryExamples (pureCallbacks)

/-- Ordinary finite input derives its plain invariant from the source record. -/
def pureBody (value : Value) (symbol : Nat) : Body Bool Nat Nat Value :=
  source (RecursiveCompleteExample.pureBody value symbol) (by intro roots plain; rfl)

/-- Occurrences preserve the current root's plain fields. -/
def recur (key : Bool) : Body Bool Nat Nat Nat :=
  occurrence pureCallbacks (fun _ => ⟨none, .pure⟩) key

/-- The delayed branch applies an ordinary function to the other recursive key. -/
def branches : Fin 2 → Body Bool Nat Nat Nat
  | ⟨0, _⟩ => pureBody 0 0
  | ⟨1, _⟩ => label 10 (ap (pureBody Nat.succ 20) (recur true))

/-- Both plain bodies expose complete support, diagnostic, guard, and runtime fields. -/
def bodies : Bool → Body Bool Nat Nat Nat
  | false => nary 2 branches
  | true => label 11 (recur false)

/-- The original application compilers occur in all four views of the delayed branch. -/
theorem application_checked :
    (ap (pureBody Nat.succ 20) (recur true)).complete.runtime.template.checked =
      RecursiveJoinBodyFields.ap (RecursiveCompleteExample.pureBody Nat.succ 20).runtime.template.checked
        (RecursiveCompleteExample.occurrence true).runtime.template.checked := rfl

/-- Application keeps the missing probe callback and the complete term rebuild distinct. -/
theorem application_phases :
    (ap (pureBody Nat.succ 20) (recur true)).complete.runtime.template.metadata
      (fun _ => RecursiveJoinRuntime.placeholder) = ⟨false, false, false⟩ ∧
    (ap (pureBody Nat.succ 20) (recur true)).complete.runtime.template.metadata
      (fun _ => RecursiveJoinRuntime.termPlaceholder) = ⟨false, false, true⟩ := by
  decide +kernel

/-- Both completed family members retain ordinary sampling and complete term fields. -/
theorem runtime_fields (key : Bool) :
    RecursiveRuntimeOrigins.memberMetadata [false, true]
      (RecursiveRuntimeVerified.templates (fun key => (bodies key).complete.runtime)) key = ⟨false, false, true⟩ := by
  cases key <;> decide +kernel

/-- The delayed application has one member of mass one after two size units. -/
theorem delayed_value :
    let valueProgram := fun key => (bodies key).complete.runtime.template.checked.body.value
    Decoder.values (KeyedSource.family valueProgram 2 false).members.plan = [1] ∧
      (KeyedSource.family valueProgram 2 false).mass = 1 := by
  decide +kernel

end MicroCFTA.RecursivePlainApplicationExamples
