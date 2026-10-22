import MicroCFTA.InternedGuardedLanguageSupport

/-!
# Actual constructor effects preserve independent guarded meaning

The existing normalization proofs apply to the stored-payload least-language
interpretation. Coherent free-name support also proves actual unused-binder
and bare-self cleanup. No cold-reader language or allocation-order premise
defines the result.
-/
namespace MicroCFTA.InternedGuardedLanguage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol Language

/-- Actual node normalization retains precisely the independent guarded meanings of its source edges. -/
theorem makeNode_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (term : Term Symbol) :
    meaning holds environment (run (makeNode edges) state).1 term ↔
      ∃ edge ∈ edges, MergedColdInterpretation.EdgeMeaning (meaning holds environment) holds edge term :=
  MergedColdInterpretation.makeNode_exact state facts (meaning holds environment) edges resident holds (laws holds environment) term

/-- Actual union normalization retains exactly the independent guarded language of its original operands. -/
theorem makeUnion_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (available : Values state values) (term : Term Symbol) :
    meaning holds environment (run (makeUnion values) state).1 term ↔ ∃ value ∈ values, meaning holds environment value term :=
  MergedColdInterpretation.makeUnion_common state facts (meaning holds environment) values available holds (laws holds environment) term

/-- Removing an unused actual stored Mu preserves the complete independent guarded language. -/
theorem unused_mu (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) (unused : .interned entry.identity ∉ body.free) :
    meaning holds environment (.mu entry body depth ordinary) = meaning holds environment body := by
  rw [meaning]
  apply Eq.trans (b := BinderLanguage.least (fun _ => meaning holds environment body))
  · apply BinderLanguage.least_congr
    intro language term
    apply iff_of_eq
    apply congrFun
    apply meaning_free holds body state coherent available
    intro name member
    have different : name ≠ .interned entry.identity := fun equal => unused (equal ▸ member)
    simp only [bind, different, ↓reduceIte]
  · exact BinderLanguage.least_constant _

/-- An actual Mu whose body is its own bare reference has no accepted finite term. -/
theorem self_mu (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (depth ordinary : Value Symbol Guard) :
    meaning holds environment (.mu entry (.reference (.interned entry.identity)) depth ordinary) = meaning holds environment .empty := by
  funext term
  apply propext
  simp only [meaning, bind, ↓reduceIte]
  constructor
  · intro accepted
    exact accepted (fun _ => False) (fun _ => id)
  · intro impossible
    exact impossible.elim

/-- Actual smart cleanup retains the independent language of every coherent available record. -/
theorem cleanup_exact (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    meaning holds environment (cleanup value) = meaning holds environment value := by
  cases value with
  | empty | reference | node | union => rfl
  | mu entry body depth ordinary =>
      by_cases unused : .interned entry.identity ∉ body.free
      · rw [cleanup, ite_eq_left unused]
        exact (unused_mu holds environment entry body depth ordinary state coherent
          (available.children body (by simp [children])) unused).symm
      · rw [cleanup, ite_eq_right unused]
        by_cases bare : body.referenceOf = .ref (.interned entry.identity)
        · rw [ite_eq_left bare]
          have same : body = .reference (.interned entry.identity) := by
            cases body <;> simp_all [Value.referenceOf]
          rw [same]
          exact (self_mu holds environment entry depth ordinary).symm
        · rw [ite_eq_right bare]

/-- Both actual raw and smart finish paths retain independent guarded meaning. -/
theorem finish_exact (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (smart : Bool)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) :
    meaning holds environment (InternedNestedConstruction.finish smart value) = meaning holds environment value := by
  cases smart with
  | false => rfl
  | true => exact cleanup_exact holds environment value state coherent available

end MicroCFTA.InternedGuardedLanguage
