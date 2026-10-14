import MicroCFTA.BinderBudgetLanguage
import MicroCFTA.InternedGuardedLanguage

/-!
# Guarded stored meaning with a Mu-unfolding budget

This interpretation retains complete guards and ordered children. Every raw
stored Mu consumes one unfolding step. Ordinary constructors retain the
budget. Metadata and cache allocation do not define this interpretation.
-/
namespace MicroCFTA.InternedGuardedBudget
open InternedConstructorTemplates InternedBinderProtocol Language
open BinderBudgetLanguage (Lang Included Upward)

/-- Each actual reference supplies a language for every unfolding budget. -/
abbrev Env (Symbol : Type) := Reference → Lang Symbol

/-- An actual stored binder replaces its own reference language. -/
def bind (environment : Env Symbol) (name : Reference) (language : Lang Symbol) : Env Symbol :=
  fun other => if other = name then language else environment other

mutual
/-- Interpret actual stored payloads with one budget step for each Mu unfolding. -/
def meaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) : Value Symbol Guard → Lang Symbol
  | .empty => fun _ _ => False
  | .reference name => environment name
  | .node _ edges _ _ => fun budget term => ∃ edge : {edge // edge ∈ edges}, edgeMeaning holds environment edge.val budget term
  | .union _ members _ _ => fun budget term => ∃ member : {member // member ∈ members}, meaning holds environment member.val budget term
  | .mu entry body _ _ => BinderBudgetLanguage.mu (fun language => meaning holds (bind environment (.interned entry.identity) language) body)
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Complete guarded edges retain the common budget for every ordered child. -/
def edgeMeaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) : EdgeValue Symbol Guard → Lang Symbol
  | .mk entry children => fun budget term => ∃ terms, term = .node entry.key.symbol terms ∧
      forest holds environment budget children terms ∧ holds entry.key.constraint term = true
termination_by edge => sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered child forests retain their common unfolding bound. -/
def forest (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (budget : Nat) :
    List (Value Symbol Guard) → List (Term Symbol) → Prop
  | [], [] => True
  | child :: rest, term :: terms => meaning holds environment child budget term ∧ forest holds environment budget rest terms
  | _, _ => False
termination_by children _ => sizeOf children
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Stored budget languages are positive in every free-reference budget language. -/
theorem meaning_mono (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (before after : Env Symbol)
    (included : ∀ name, Included (before name) (after name)) : Included (meaning holds before value) (meaning holds after value) := by
  cases value with
  | empty => rw [meaning, meaning]; exact fun _ _ impossible => impossible
  | reference name => simpa only [meaning] using included name
  | node entry edges depth free =>
      rw [meaning, meaning]
      rintro budget term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_mono holds edge.val before after included budget term accepted⟩
  | union entry members depth free =>
      rw [meaning, meaning]
      rintro budget term ⟨member, accepted⟩
      exact ⟨member, meaning_mono holds member.val before after included budget term accepted⟩
  | mu entry body depth ordinary =>
      rw [meaning, meaning]
      apply BinderBudgetLanguage.mu_mono
      intro language
      apply meaning_mono holds body
      intro name budget term accepted
      by_cases same : name = .interned entry.identity
      · simpa only [bind, same, ↓reduceIte] using accepted
      · simpa only [bind, same, ↓reduceIte] using included name budget term (by simpa only [bind, same, ↓reduceIte] using accepted)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Complete guarded edge languages retain inclusion at every fixed unfolding bound. -/
theorem edgeMeaning_mono (holds : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (before after : Env Symbol)
    (included : ∀ name, Included (before name) (after name)) : Included (edgeMeaning holds before edge) (edgeMeaning holds after edge) := by
  cases edge with
  | mk entry children =>
      rw [edgeMeaning, edgeMeaning]
      rintro budget term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_mono holds children terms before after included budget runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordered child forests retain inclusion at the same unfolding bound. -/
theorem forest_mono (holds : Guard → Term Symbol → Bool) (children : List (Value Symbol Guard)) (terms : List (Term Symbol))
    (before after : Env Symbol) (included : ∀ name, Included (before name) (after name)) (budget : Nat)
    (accepted : forest holds before budget children terms) : forest holds after budget children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨meaning_mono holds child before after included budget term accepted.1,
            forest_mono holds rest terms before after included budget accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

mutual
/-- Upward reference inputs make every stored language upward in its unfolding budget. -/
theorem meaning_upward (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (environment : Env Symbol)
    (upward : ∀ name, Upward (environment name)) : Upward (meaning holds environment value) := by
  cases value with
  | empty => rw [meaning]; exact fun _ _ _ _ impossible => impossible
  | reference name => simpa only [meaning] using upward name
  | node entry edges depth free =>
      rw [meaning]
      rintro before after bounded term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_upward holds edge.val environment upward before after bounded term accepted⟩
  | union entry members depth free =>
      rw [meaning]
      rintro before after bounded term ⟨member, accepted⟩
      exact ⟨member, meaning_upward holds member.val environment upward before after bounded term accepted⟩
  | mu => rw [meaning]; exact BinderBudgetLanguage.mu_upward _
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Upward child languages make every complete edge language upward. -/
theorem edgeMeaning_upward (holds : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (environment : Env Symbol)
    (upward : ∀ name, Upward (environment name)) : Upward (edgeMeaning holds environment edge) := by
  cases edge with
  | mk entry children =>
      rw [edgeMeaning]
      rintro before after bounded term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_upward holds children terms environment upward before after bounded runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Increasing a common unfolding bound retains the same ordered forest. -/
theorem forest_upward (holds : Guard → Term Symbol → Bool) (children : List (Value Symbol Guard)) (terms : List (Term Symbol))
    (environment : Env Symbol) (upward : ∀ name, Upward (environment name)) (before after : Nat) (bounded : before ≤ after)
    (accepted : forest holds environment before children terms) : forest holds environment after children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨meaning_upward holds child environment upward before after bounded term accepted.1,
            forest_upward holds rest terms environment upward before after bounded accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

/-- A stored Mu accepts exactly a body run with a strictly smaller unfolding budget. -/
theorem mu_unfold (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Cache.Interned NodeKey) (body depth ordinary : Value Symbol Guard) (budget : Nat) (term : Term Symbol) :
    meaning holds environment (.mu entry body depth ordinary) budget term ↔
      ∃ smaller, smaller < budget ∧ meaning holds
        (bind environment (.interned entry.identity) (meaning holds environment (.mu entry body depth ordinary))) body smaller term := by
  simp only [meaning]
  apply BinderBudgetLanguage.mu_unfold
  intro before after included
  apply meaning_mono holds body
  intro name bound subterm accepted
  by_cases same : name = .interned entry.identity
  · simpa only [bind, same, ↓reduceIte] using included bound subterm (by simpa only [bind, same, ↓reduceIte] using accepted)
  · simpa only [bind, same, ↓reduceIte] using accepted

/-- A stored binder cannot accept any term without unfolding budget. -/
theorem mu_zero (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Cache.Interned NodeKey) (body depth ordinary : Value Symbol Guard) (term : Term Symbol) :
    ¬ meaning holds environment (.mu entry body depth ordinary) 0 term := by
  intro accepted
  obtain ⟨smaller, impossible, _⟩ := (mu_unfold holds environment entry body depth ordinary 0 term).mp accepted
  omega

/-- Fixed-budget forests have the exact ordinary ordered child-run relation. -/
theorem forest_all (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (budget : Nat)
    (children : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    forest holds environment budget children terms ↔ All₂ (fun value term => meaning holds environment value budget term) children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [forest] <;> constructor <;> intro accepted <;> first | exact .nil | trivial | cases accepted
  | cons child rest ih =>
      cases terms with
      | nil => simp only [forest]; constructor <;> intro accepted <;> cases accepted
      | cons term terms =>
          rw [forest]
          constructor
          · rintro ⟨head, tail⟩; exact .cons head ((ih terms).mp tail)
          · intro accepted; cases accepted with | cons head tail => exact ⟨head, (ih terms).mpr tail⟩

/-- A complete edge at a fixed budget meets the ordinary constructor edge law. -/
theorem edgeMeaning_all (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (budget : Nat)
    (edge : EdgeValue Symbol Guard) (term : Term Symbol) :
    edgeMeaning holds environment edge budget term ↔
      MergedColdInterpretation.EdgeMeaning (fun value => meaning holds environment value budget) holds edge term := by
  cases edge with
  | mk entry children =>
      simp only [edgeMeaning, MergedColdInterpretation.EdgeMeaning, EdgeValue.entry, EdgeValue.children]
      exact exists_congr (fun terms => and_congr Iff.rfl
        (and_congr (forest_all holds environment budget children terms) Iff.rfl))

/-- Each fixed budget meets the actual ordinary constructor language laws. -/
theorem laws (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (budget : Nat) :
    MergedColdInterpretation.Laws (fun value => meaning holds environment value budget) holds := by
  constructor
  · intro term
    simp only [meaning, not_false_eq_true]
  · intro entry edges depth free term
    rw [meaning]
    constructor
    · rintro ⟨⟨edge, member⟩, accepted⟩
      exact ⟨edge, member, (edgeMeaning_all holds environment budget edge term).mp accepted⟩
    · rintro ⟨edge, member, accepted⟩
      exact ⟨⟨edge, member⟩, (edgeMeaning_all holds environment budget edge term).mpr accepted⟩
  · intro entry members depth free term
    rw [meaning]
    constructor
    · rintro ⟨⟨member, present⟩, accepted⟩
      exact ⟨member, present, accepted⟩
    · rintro ⟨member, present, accepted⟩
      exact ⟨⟨member, present⟩, accepted⟩

end MicroCFTA.InternedGuardedBudget
