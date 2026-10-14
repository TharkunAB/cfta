import MicroCFTA.InternedGuardedBudgetSmartFinish
import MicroCFTA.InternedDeepLocalNormal

/-!
# Exact budgets of normalized stored binder finish

A normalized callback has only deep local occurrences or a bare self body.
The existing local invariant therefore decides whether smart finish retains
the raw Mu or returns the body with an empty local language.
-/
namespace MicroCFTA.InternedGuardedBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedDeepFreeDepth InternedDeepLocalNormal
open Language

/-- Actual normalized binder finish has the exact deep-local budget branch. -/
theorem finish_local_exact (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (localNormal : Local (.interned entry.identity) body) :
    meaning holds environment (InternedNestedConstruction.finish smart (.mu entry body depth ordinary)) =
      if !smart || decide (.interned entry.identity ∈ deepNames body) then
        meaning holds environment (.mu entry body depth ordinary)
      else meaning holds (bind environment (.interned entry.identity) (fun _ _ => False)) body := by
  cases smart with
  | false => simp only [Bool.not_false, Bool.true_or, Bool.false_eq_true, ↓reduceIte, InternedNestedConstruction.finish]
  | true =>
      simp only [Bool.not_true, Bool.false_or]
      by_cases used : .interned entry.identity ∈ deepNames body
      · have free := InternedDeepFreeNormalization.deep_free body state coherent available _ used
        have nonbare : body.referenceOf ≠ .ref (.interned entry.identity) := by
          intro same
          have bare := (InternedConstructorTemplates.referenceOf_self_iff _ body).mp same
          simp only [bare, deepNames, List.not_mem_nil] at used
        simp only [used, decide_true, ↓reduceIte, InternedNestedConstruction.finish, cleanup, free,
          not_true_eq_false, nonbare]
      · simp only [used, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases free : .interned entry.identity ∈ body.free
        · rcases localNormal free with impossible | bare
          · exact (used impossible).elim
          · subst body
            simp only [InternedNestedConstruction.finish, cleanup, Value.free, List.mem_singleton,
              not_true_eq_false, ↓reduceIte, Value.referenceOf, meaning, bind]
        · rw [InternedNestedConstruction.finish, cleanup, ite_eq_left free]
          apply meaning_free holds body state coherent available
          intro name member
          have different : name ≠ .interned entry.identity := fun same => free (same ▸ member)
          simp only [bind, different, ↓reduceIte]

end MicroCFTA.InternedGuardedBudget
