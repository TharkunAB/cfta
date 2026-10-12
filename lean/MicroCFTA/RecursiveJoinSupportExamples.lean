import MicroCFTA.RecursiveJoinSupportFamily
import MicroCFTA.RecursiveJoinFamilyExamples

/-!
# Shared-binder support for the concrete heterogeneous mutual family

These support graphs are assembled independently of the term decoder.
The family includes flat alternatives, retained masses, source label
closing, two recursive keys, and a nested nullary join argument.
-/
namespace MicroCFTA.RecursiveJoinSupportExamples
open Language GeneratorCombinators BinderLanguage SupportGraph
open RecursiveCallbackTermination (EngineTerm)
open RecursiveNaryExamples (pureCallbacks pure_exact)
open RecursiveJoinSupportBody

/-- A pure correlated operand retains its exact ordinary finite singleton support. -/
def pureBody (value : Value) (symbol : Nat) : Body Bool Nat Nat Value :=
  finite pureCallbacks (.pure (value, .node (.user symbol) [])) (pure_exact _)
    (RecursiveJoinSupportView.ordinary ⟨.user symbol, fun _ => True⟩ [] (by rfl)) (by
      intro environment term
      change meaning environment (edge (.user symbol) []) term ↔ _
      rw [SupportClosing.leaf_exact]
      simp [FiniteSource.classMembers])

/-- A retained pure alternative has the same singleton support at either mass. -/
def retainedBody (mass : Rat) (positive : 0 < mass) : Body Bool Nat Nat Nat :=
  retained pureCallbacks (fun _ => mass) (fun _ => positive) (.pure (0, .node .pure [])) (pure_exact _)
    RecursiveJoinSupportView.pure (by
      intro environment term
      change meaning environment (edge .pure []) term ↔ _
      rw [SupportClosing.leaf_exact]
      simp [FiniteSource.classMembers])

/-- A nested nullary join remains an actual keyed support graph. -/
def flag : Body Bool Nat Nat Bool := join 7 (pureBody true 1) .nil

/-- The operation consumes Boolean and natural arguments in their original order. -/
def operation : Body Bool Nat Nat (Bool → Nat → Nat) :=
  pureBody (fun flag value => if flag then value + 1 else value) 20

/-- Each flat alternative constructs support separately from its decoder fields. -/
def branches : Fin 3 → Body Bool Nat Nat Nat
  | ⟨0, _⟩ => retainedBody 9 (by decide)
  | ⟨1, _⟩ => retainedBody 1 (by decide)
  | ⟨2, _⟩ => label 10 (join 5 operation (.cons flag (.cons (occurrence pureCallbacks true) .nil)))

/-- Both source bodies retain the actual support closing operations around their joins. -/
def program : Bool → Body Bool Nat Nat Nat
  | false => nary 3 branches
  | true => label 11 (join 6 (pureBody Nat.succ 21) (.cons (occurrence pureCallbacks false) .nil))

/-- Adding independent support fields preserves the complete existing checked program. -/
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

/-- The independently supported program retains every compiled family recipe. -/
theorem lower_same : RecursiveJoinSupportFamily.lower program =
    RecursiveJoinInverse.lower RecursiveJoinFamilyExamples.program :=
  congrArg (fun program key => (program key).body) checked_same

/-- The concrete source key codes identify exactly one body each. -/
theorem code_injective : Function.Injective RecursiveJoinFamilyExamples.code := by
  intro first second same
  cases first <;> cases second <;> simp_all [RecursiveJoinFamilyExamples.code]

/-- The independently decoded delayed term belongs to the actual shared-binder support. -/
theorem delayed_accepted (environment : Env (Label Nat)) (token : Nat) :
    meaning environment
      (RecursiveJoinSupportFamily.memberGraph token RecursiveJoinFamilyExamples.code RecursiveJoinFamilyExamples.keys program false)
      RecursiveJoinFamilyExamples.delayedTerm := by
  have accepted : ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (RecursiveJoinSupportFamily.lower program) key)
      (KeyedSource.minima RecursiveJoinFamilyExamples.keys RecursiveJoinFamilyExamples.complete
        (RecursiveJoinFamily.valueProgram (RecursiveJoinSupportFamily.lower program))) = true := by
    rw [lower_same]
    exact RecursiveJoinFamilyExamples.accepted
  exact RecursiveJoinSupportFamily.selected_accepted token RecursiveJoinFamilyExamples.code code_injective
    RecursiveJoinFamilyExamples.keys RecursiveJoinFamilyExamples.complete program accepted environment false 2 0 _
    (by simpa only [RecursiveJoinSupportFamily.termProgram, lower_same] using RecursiveJoinFamilyExamples.delayed_select)

/-- Every member of the shared support is an independently decoded source term at some finite size. -/
theorem all_members_exact (environment : Env (Label Nat)) (token : Nat) (key : Bool) (term : EngineTerm Nat) :
    meaning environment
      (RecursiveJoinSupportFamily.memberGraph token RecursiveJoinFamilyExamples.code RecursiveJoinFamilyExamples.keys program key) term ↔
    ∃ size, term ∈ Decoder.values
      (KeyedSource.family (RecursiveJoinFamily.termProgram RecursiveJoinFamilyExamples.code
        (RecursiveJoinInverse.lower RecursiveJoinFamilyExamples.program)) size key).members.plan := by
  have accepted : ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (RecursiveJoinSupportFamily.lower program) key)
      (KeyedSource.minima RecursiveJoinFamilyExamples.keys RecursiveJoinFamilyExamples.complete
        (RecursiveJoinFamily.valueProgram (RecursiveJoinSupportFamily.lower program))) = true := by
    rw [lower_same]
    exact RecursiveJoinFamilyExamples.accepted
  simpa only [RecursiveJoinSupportFamily.termProgram, lower_same] using
    RecursiveJoinSupportFamily.family_exact token RecursiveJoinFamilyExamples.code code_injective
      RecursiveJoinFamilyExamples.keys RecursiveJoinFamilyExamples.complete program accepted environment key term

end MicroCFTA.RecursiveJoinSupportExamples
