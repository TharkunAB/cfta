import MicroCFTA.RecursiveJoinInspectionBody
import MicroCFTA.RecursiveJoinFamilyExamples

/-!
# Named inspection fields for the heterogeneous mutual family

The named diagnostic graph uses the same typed constructors as the checked
family. Names appear on join keys and cannot alter decoding or callbacks.
-/
namespace MicroCFTA.RecursiveJoinInspectionExamples
open Language GeneratorCombinators
open RecursiveCallbackTermination (EngineTerm)
open RecursiveNaryExamples (pureCallbacks pure_exact)
open RecursiveJoinInspectionBody

/-- An atomic generator keeps its independently supplied finite inspection. -/
def pureBody (value : Value) (symbol : Nat) : Body Bool Nat Nat Value :=
  ofNary pureCallbacks (fun _ => ⟨none, .ordinary (RecursiveJoinInspection.edge (.user symbol) [])⟩)
    (.finite (.pure (value, .node (.user symbol) []))) (pure_exact _) (by
      simp [LeavesValid, RecursiveJoinInspection.Valid, RecursiveJoinInspection.OrdinaryGraph,
        RecursiveJoinInspection.edge, RecursiveJoinInspection.Ordinary, SupportClosing.ordinary])

/-- Retained weights leave the finite pure diagnostic graph unchanged. -/
def retained (mass : Rat) (positive : 0 < mass) : Body Bool Nat Nat Nat :=
  ofNary pureCallbacks (fun _ => ⟨none, .pure⟩)
    (.retained (fun _ => mass) (fun _ => positive) (.pure (0, .node .pure []))) (pure_exact _) (by
      simp [LeavesValid, RecursiveJoinInspection.Valid])

/-- Recursive diagnostics use their own named occurrence context. -/
def occurrence (key : Bool) : Body Bool Nat Nat Nat :=
  ofNary pureCallbacks (fun _ => ⟨none, .pure⟩) (.occurrence key) True.intro True.intro

/-- The Boolean operand names the keys of its enclosing heterogeneous join. -/
def flag : Body Bool Nat Nat Bool := named (some "flag") (join 7 (pureBody true 1) .nil)

/-- The operation's name does not replace the names of its argument keys. -/
def operation : Body Bool Nat Nat (Bool → Nat → Nat) :=
  named (some "operation") (pureBody (fun flag value => if flag then value + 1 else value) 20)

/-- Each source alternative retains its complete original diagnostic branch. -/
def branches : Fin 3 → Body Bool Nat Nat Nat
  | ⟨0, _⟩ => retained 9 (by decide)
  | ⟨1, _⟩ => retained 1 (by decide)
  | ⟨2, _⟩ => label 10 (join 5 operation (.cons flag (.cons (named (some "value") (occurrence true)) .nil)))

/-- Both bodies compile against the separate diagnostic family context. -/
def program : Bool → Body Bool Nat Nat Nat
  | false => nary 3 branches
  | true => label 11 (join 6 (pureBody Nat.succ 21) (.cons (occurrence false) .nil))

/-- The additional names and diagnostics leave all checked fields unchanged. -/
theorem checked_same : (fun key => (program key).checked) = RecursiveJoinFamilyExamples.program := by
  funext key
  cases key with
  | true => rfl
  | false =>
      change RecursiveJoinBodyFields.nary 3 (fun index => (branches index).checked) =
        RecursiveJoinBodyFields.nary 3 RecursiveJoinFamilyExamples.branches
      congr 1
      funext ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> rfl

/-- The typed join retains the two distinct argument names in source order. -/
theorem heterogeneous_names (roots : Bool → RecursiveJoinInspection.Inspection Nat) :
    ((join 5 operation (.cons flag (.cons (named (some "value") (occurrence true)) .nil))).inspect roots).layer =
      .join 5 (operation.inspect roots).layer
        [(some "flag", (flag.inspect roots).layer), (some "value", (roots true).layer)] := rfl

/-- The complete mutually recursive diagnostic context derives every closing invariant. -/
theorem valid_family (token : Nat) (names : Bool → Option String) (key : Bool) :
    RecursiveJoinInspection.Valid ((program key).inspect
      (fun key => RecursiveJoinInspection.occurrence token (RecursiveJoinFamilyExamples.code key) (names key))).layer :=
  family_body_valid token RecursiveJoinFamilyExamples.code names program key

/-- The independent source decoder still selects the same delayed heterogeneous join term. -/
theorem delayed_decoder_unchanged :
    Decoder.decode (KeyedSource.family
      (RecursiveJoinFamily.termProgram RecursiveJoinFamilyExamples.code
        (RecursiveJoinInverse.lower (fun key => (program key).checked))) 2 false).members.plan 0 =
      some RecursiveJoinFamilyExamples.delayedTerm := by
  rw [checked_same]
  exact RecursiveJoinFamilyExamples.delayed_select

end MicroCFTA.RecursiveJoinInspectionExamples
