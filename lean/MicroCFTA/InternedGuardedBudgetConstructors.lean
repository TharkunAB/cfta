import MicroCFTA.InternedGuardedBudgetSupport

/-!
# Actual constructors retain unfolding budgets

Ordinary node and union normalization preserve each fixed-budget language.
An unused raw Mu still costs one step. Smart cleanup can remove that step,
so its budget law is inclusion from the original value to the result.
-/
namespace MicroCFTA.InternedGuardedBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol Language

/-- Actual node normalization preserves every fixed-budget guarded edge language. -/
theorem makeNode_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (budget : Nat) (term : Term Symbol) :
    meaning holds environment (run (makeNode edges) state).1 budget term ↔
      ∃ edge ∈ edges, MergedColdInterpretation.EdgeMeaning (fun value => meaning holds environment value budget) holds edge term :=
  MergedColdInterpretation.makeNode_exact state facts (fun value => meaning holds environment value budget)
    edges resident holds (laws holds environment budget) term

/-- Actual union normalization preserves every fixed-budget operand language. -/
theorem makeUnion_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (available : Values state values) (budget : Nat) (term : Term Symbol) :
    meaning holds environment (run (makeUnion values) state).1 budget term ↔
      ∃ value ∈ values, meaning holds environment value budget term :=
  MergedColdInterpretation.makeUnion_common state facts (fun value => meaning holds environment value budget)
    values available holds (laws holds environment budget) term

/-- An unused raw stored Mu has exactly one shifted body budget language. -/
theorem unused_mu (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) (unused : .interned entry.identity ∉ body.free) :
    meaning holds environment (.mu entry body depth ordinary) = BinderBudgetLanguage.shift (meaning holds environment body) := by
  rw [meaning]
  apply Eq.trans (b := BinderBudgetLanguage.mu (fun _ => meaning holds environment body))
  · apply congrArg BinderBudgetLanguage.mu
    funext language
    apply meaning_free holds body state coherent available
    intro name member
    have different : name ≠ .interned entry.identity := fun equal => unused (equal ▸ member)
    simp only [bind, different, ↓reduceIte]
  · exact BinderBudgetLanguage.mu_constant _

/-- A bare stored recursive self body has no finite accepted term at any budget. -/
theorem self_mu (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (depth ordinary : Value Symbol Guard) :
    meaning holds environment (.mu entry (.reference (.interned entry.identity)) depth ordinary) =
      meaning holds environment .empty := by
  simp only [meaning, bind, ↓reduceIte]
  exact BinderBudgetLanguage.mu_self

/-- Actual smart cleanup retains every accepted term without increasing its required budget. -/
theorem cleanup_refines (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (upward : ∀ name, BinderBudgetLanguage.Upward (environment name)) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    BinderBudgetLanguage.Included (meaning holds environment value) (meaning holds environment (cleanup value)) := by
  cases value with
  | empty | reference | node | union => exact fun _ _ accepted => accepted
  | mu entry body depth ordinary =>
      by_cases unused : .interned entry.identity ∉ body.free
      · rw [cleanup, ite_eq_left unused, unused_mu holds environment entry body depth ordinary state coherent
          (available.children body (by simp [children])) unused]
        rintro budget term ⟨smaller, less, accepted⟩
        exact meaning_upward holds body environment upward smaller budget (Nat.le_of_lt less) term accepted
      · rw [cleanup, ite_eq_right unused]
        by_cases bare : body.referenceOf = .ref (.interned entry.identity)
        · rw [ite_eq_left bare]
          have same : body = .reference (.interned entry.identity) := by
            cases body <;> simp_all [Value.referenceOf]
          rw [same, self_mu]
          exact fun _ _ accepted => accepted
        · rw [ite_eq_right bare]
          exact fun _ _ accepted => accepted

/-- Both actual finish paths retain terms at their original unfolding budgets. -/
theorem finish_refines (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (upward : ∀ name, BinderBudgetLanguage.Upward (environment name)) (smart : Bool)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    BinderBudgetLanguage.Included (meaning holds environment value)
      (meaning holds environment (InternedNestedConstruction.finish smart value)) := by
  cases smart with
  | false => exact fun _ _ accepted => accepted
  | true => exact cleanup_refines holds environment upward value state coherent available

end MicroCFTA.InternedGuardedBudget
