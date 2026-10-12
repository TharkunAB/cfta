import MicroCFTA.RecursiveCompleteRecord
import MicroCFTA.RecursiveJoinSupportExamples
import MicroCFTA.RecursiveJoinInspectionExamples

/-!
# One complete heterogeneous recursive family

The same constructors build support, inspection, runtime flags, original
occurrence checks, values, terms, masses, and inverse callbacks. Independent
existing decoders retain their exact results through the combined record.
-/
namespace MicroCFTA.RecursiveCompleteExample
open Language GeneratorCombinators BinderLanguage SupportGraph
open RecursiveCompleteRecord
open RecursiveNaryExamples (pureCallbacks pure_exact)

/-- A pure source supplies local singleton support and unweighted rank laws. -/
def pureBody (value : Value) (symbol : Nat) : Body Bool Nat Nat Value :=
  finite pureCallbacks (.pure (value, .node (.user symbol) [])) (pure_exact _) false
    (by
      intro _ size
      cases size with
      | zero => exact RecursiveUniformRuntime.uniform_counting [(value, Term.node (Label.user symbol) [])]
      | succ _ => exact RecursiveUniformRuntime.uniform_counting [])
    (RecursiveJoinSupportView.ordinary ⟨.user symbol, fun _ => True⟩ [] (by rfl))
    (by
      intro environment term
      change meaning environment (edge (.user symbol) []) term ↔ _
      rw [SupportClosing.leaf_exact]
      simp [FiniteSource.classMembers])
    (fun _ => ⟨none, .ordinary (RecursiveJoinInspection.edge (.user symbol) [])⟩)
    (by simp [RecursiveJoinInspection.Valid, RecursiveJoinInspection.OrdinaryGraph,
      RecursiveJoinInspection.edge, RecursiveJoinInspection.Ordinary, SupportClosing.ordinary])

/-- A retained singleton keeps its exact source mass and its independent pure graph. -/
def retainedBody (mass : Rat) (positive : 0 < mass) : Body Bool Nat Nat Nat :=
  retained pureCallbacks (fun _ => mass) (fun _ => positive) (.pure (0, .node .pure [])) (pure_exact _) false
    RecursiveJoinSupportView.pure
    (by
      intro environment term
      change meaning environment (edge .pure []) term ↔ _
      rw [SupportClosing.leaf_exact]
      simp [FiniteSource.classMembers])
    (fun _ => ⟨none, .pure⟩) (by simp [RecursiveJoinInspection.Valid])

/-- A recursive key is read through all four record contexts. -/
def occurrence (key : Bool) : Body Bool Nat Nat Nat :=
  RecursiveCompleteRecord.occurrence pureCallbacks (fun _ => ⟨none, .pure⟩) key

/-- The heterogeneous argument retains its own nullary join and display name. -/
def flag : Body Bool Nat Nat Bool := named (some "flag") (join 7 (pureBody true 1) .nil)

/-- The operation uses different Boolean and natural argument types. -/
def operation : Body Bool Nat Nat (Bool → Nat → Nat) :=
  named (some "operation") (pureBody (fun flag value => if flag then value + 1 else value) 20)

/-- One complete record is built for each source branch. -/
def branches : Fin 3 → Body Bool Nat Nat Nat
  | ⟨0, _⟩ => retainedBody 9 (by decide)
  | ⟨1, _⟩ => retainedBody 1 (by decide)
  | ⟨2, _⟩ => label 10 (join 5 operation (.cons flag (.cons (named (some "value") (occurrence true)) .nil)))

/-- Both mutual bodies use the complete record constructors. -/
def program : Bool → Body Bool Nat Nat Nat
  | false => nary 3 branches
  | true => label 11 (join 6 (pureBody Nat.succ 21) (.cons (occurrence false) .nil))

/-- Every generated field uses the independently established checked program. -/
theorem checked_same : checked program = RecursiveJoinFamilyExamples.program := by
  funext key
  cases key with
  | true => rfl
  | false =>
      change RecursiveJoinBodyFields.nary 3 (fun index => (branches index).runtime.template.checked) =
        RecursiveJoinBodyFields.nary 3 RecursiveJoinFamilyExamples.branches
      congr 1
      funext ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> rfl

/-- Complete construction reproduces the independently assembled support records. -/
theorem support_same : (fun key => (program key).support) = RecursiveJoinSupportExamples.program := by
  funext key
  cases key with
  | true => rfl
  | false =>
      change RecursiveJoinSupportBody.nary 3 (fun index => (branches index).support) =
        RecursiveJoinSupportBody.nary 3 RecursiveJoinSupportExamples.branches
      congr 1
      funext ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> rfl

/-- Complete construction also reproduces the independently named diagnostic records. -/
theorem inspection_same : (fun key => (program key).inspection) = RecursiveJoinInspectionExamples.program := by
  funext key
  cases key with
  | true => rfl
  | false =>
      change RecursiveJoinInspectionBody.nary 3 (fun index => (branches index).inspection) =
        RecursiveJoinInspectionBody.nary 3 RecursiveJoinInspectionExamples.branches
      congr 1
      funext ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl <;> rfl

/-- The complete record's delayed decoded term belongs to its own independently built support. -/
theorem delayed_supported (environment : Env (Label Nat)) (token : Nat) :
    meaning environment (RecursiveJoinSupportFamily.memberGraph token RecursiveJoinFamilyExamples.code
      RecursiveJoinFamilyExamples.keys (fun key => (program key).support) false) RecursiveJoinFamilyExamples.delayedTerm := by
  rw [support_same]
  exact RecursiveJoinSupportExamples.delayed_accepted environment token

/-- The complete record retains the delayed member and its exact global inverse rank. -/
theorem delayed_roundtrip :
    RecursiveJoinQuery.boundedDecode RecursiveJoinFamilyExamples.code (checked program) false 2 2 =
      some RecursiveJoinFamilyExamples.delayedTerm ∧
    RecursiveJoinQuery.boundedQuery RecursiveJoinFamilyExamples.code (checked program) false 2 .whole
      [RecursiveJoinFamilyExamples.delayedTerm] = [2] := by
  rw [checked_same]
  exact ⟨RecursiveJoinFamilyExamples.bounded_delayed.2.2, RecursiveJoinFamilyExamples.bounded_delayed.1⟩

/-- Both source keys retain the family weight marker and complete term fields. -/
theorem runtime_fields (key : Bool) :
    let fields := RecursiveRuntimeOrigins.memberMetadata RecursiveJoinFamilyExamples.keys
      (RecursiveRuntimeVerified.templates (fun key => (program key).runtime)) key
    fields.weighted = true ∧ fields.massWeighted = true ∧ fields.terms = true := by
  cases key <;> decide +kernel

/-- The complete record keeps the independently established nine-to-one class distribution. -/
theorem delayed_mass :
    (KeyedSource.family (RecursiveJoinFamily.valueProgram (RecursiveJoinInverse.lower (checked program))) 2 false).mass = 10 ∧
    (KeyedSource.family (RecursiveJoinFamily.valueProgram (RecursiveJoinInverse.lower (checked program))) 2 false).members.sampling.ranked =
      [(9 / 10, (0, 2)), (1 / 10, (1, 2))] := by
  rw [checked_same]
  exact RecursiveJoinFamilyExamples.delayed_mass

end MicroCFTA.RecursiveCompleteExample
