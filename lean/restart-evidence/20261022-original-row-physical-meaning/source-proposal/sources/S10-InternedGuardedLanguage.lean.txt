import MicroCFTA.BinderLanguage
import MicroCFTA.MergedColdInterpretation

/-!
# Independent guarded language of actual stored records

This interpretation reads stored bodies and complete edge payloads. A Mu
denotes the least language of its body at its own interned name. Probe
metadata, cache allocation, and the cold reader do not define this meaning.
-/
namespace MicroCFTA.InternedGuardedLanguage
open InternedConstructorTemplates InternedBinderProtocol Language
open BinderLanguage (Lang Included least)

/-- Interpret each actual source reference by a language of finite terms. -/
abbrev Env (Symbol : Type) := Reference → Lang Symbol

/-- A stored Mu replaces the language of its own actual interned reference. -/
def bind (environment : Env Symbol) (name : Reference) (language : Lang Symbol) : Env Symbol :=
  fun other => if other = name then language else environment other

mutual
/-- Interpret the actual guarded payload with positive least-language binders. -/
def meaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) : Value Symbol Guard → Lang Symbol
  | .empty => fun _ => False
  | .reference name => environment name
  | .node _ edges _ _ => fun term => ∃ edge : {edge // edge ∈ edges}, edgeMeaning holds environment edge.val term
  | .union _ members _ _ => fun term => ∃ member : {member // member ∈ members}, meaning holds environment member.val term
  | .mu entry body _ _ => least (fun language => meaning holds (bind environment (.interned entry.identity) language) body)
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Interpret the source symbol, full guard, and ordered children of one actual edge. -/
def edgeMeaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) : EdgeValue Symbol Guard → Lang Symbol
  | .mk entry children => fun term => ∃ terms, term = .node entry.key.symbol terms ∧
      forest holds environment children terms ∧ holds entry.key.constraint term = true
termination_by edge => sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Interpret ordered child forests with the same arity and term order. -/
def forest (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) :
    List (Value Symbol Guard) → List (Term Symbol) → Prop
  | [], [] => True
  | child :: rest, term :: terms => meaning holds environment child term ∧ forest holds environment rest terms
  | _, _ => False
termination_by children _ => sizeOf children
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- The independent payload meaning is monotone in each free-reference language. -/
theorem meaning_mono (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (before after : Env Symbol)
    (included : ∀ name, Included (before name) (after name)) : Included (meaning holds before value) (meaning holds after value) := by
  cases value with
  | empty => rw [meaning, meaning]; exact fun _ impossible => impossible
  | reference name => simpa only [meaning] using included name
  | node entry edges depth free =>
      rw [meaning, meaning]
      rintro term ⟨edge, accepted⟩
      exact ⟨edge, edgeMeaning_mono holds edge.val before after included term accepted⟩
  | union entry members depth free =>
      rw [meaning, meaning]
      rintro term ⟨member, accepted⟩
      exact ⟨member, meaning_mono holds member.val before after included term accepted⟩
  | mu entry body depth ordinary =>
      rw [meaning, meaning]
      apply BinderLanguage.least_mono
      intro language
      apply meaning_mono holds body
      intro name term accepted
      by_cases same : name = .interned entry.identity
      · simpa only [bind, same, ↓reduceIte] using accepted
      · simpa only [bind, same, ↓reduceIte] using included name term (by simpa only [bind, same, ↓reduceIte] using accepted)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have smaller := List.sizeOf_lt_of_mem edge.property; omega) | (have smaller := List.sizeOf_lt_of_mem member.property; omega)

/-- Increasing child reference languages preserves complete edge acceptance. -/
theorem edgeMeaning_mono (holds : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (before after : Env Symbol)
    (included : ∀ name, Included (before name) (after name)) : Included (edgeMeaning holds before edge) (edgeMeaning holds after edge) := by
  cases edge with
  | mk entry children =>
      rw [edgeMeaning, edgeMeaning]
      rintro term ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, forest_mono holds children terms before after included runs, guard⟩
termination_by sizeOf edge
decreasing_by all_goals simp_wf; all_goals omega

/-- Increasing child reference languages preserves ordered accepting forests. -/
theorem forest_mono (holds : Guard → Term Symbol → Bool) (children : List (Value Symbol Guard)) (terms : List (Term Symbol))
    (before after : Env Symbol) (included : ∀ name, Included (before name) (after name))
    (accepted : forest holds before children terms) : forest holds after children terms := by
  cases children with
  | nil => cases terms <;> simp only [forest] at accepted ⊢ <;> exact accepted
  | cons child rest =>
      cases terms with
      | nil => simp only [forest] at accepted
      | cons term terms =>
          rw [forest] at accepted ⊢
          exact ⟨meaning_mono holds child before after included term accepted.1,
            forest_mono holds rest terms before after included accepted.2⟩
termination_by sizeOf children
decreasing_by all_goals simp_wf; all_goals simp_all only; all_goals simp_wf; all_goals omega
end

/-- The independent forest relation has exactly the ordinary ordered child-run meaning. -/
theorem forest_all (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (children : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    forest holds environment children terms ↔ All₂ (meaning holds environment) children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [forest] <;> constructor <;> intro accepted <;> first | exact .nil | trivial | cases accepted
  | cons child rest ih =>
      cases terms with
      | nil => simp only [forest]; constructor <;> intro accepted <;> cases accepted
      | cons term terms =>
          rw [forest]
          constructor
          · rintro ⟨head, tail⟩
            exact .cons head ((ih terms).mp tail)
          · intro accepted
            cases accepted with
            | cons head tail => exact ⟨head, (ih terms).mpr tail⟩

/-- Each independent edge meaning retains exactly the ordinary constructor edge law. -/
theorem edgeMeaning_all (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (edge : EdgeValue Symbol Guard) (term : Term Symbol) :
    edgeMeaning holds environment edge term ↔ MergedColdInterpretation.EdgeMeaning (meaning holds environment) holds edge term := by
  cases edge with
  | mk entry children =>
      simp only [edgeMeaning, MergedColdInterpretation.EdgeMeaning, EdgeValue.entry, EdgeValue.children]
      exact exists_congr (fun terms => and_congr Iff.rfl (and_congr (forest_all holds environment children terms) Iff.rfl))

/-- Actual stored Mu bodies satisfy their independent least-language unfolding equation. -/
theorem mu_unfold (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Cache.Interned NodeKey) (body depth ordinary : Value Symbol Guard) (term : Term Symbol) :
    meaning holds environment (.mu entry body depth ordinary) term ↔
      meaning holds (bind environment (.interned entry.identity) (meaning holds environment (.mu entry body depth ordinary))) body term := by
  simp only [meaning]
  apply BinderLanguage.least_fix
  intro before after included
  apply meaning_mono holds body
  intro name subterm accepted
  by_cases same : name = .interned entry.identity
  · simpa only [bind, same, ↓reduceIte] using included subterm (by simpa only [bind, same, ↓reduceIte] using accepted)
  · simpa only [bind, same, ↓reduceIte] using accepted

/-- The independent payload interpretation meets the actual ordinary constructor language laws. -/
theorem laws (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) :
    MergedColdInterpretation.Laws (meaning holds environment) holds := by
  constructor
  · intro term
    simp only [meaning, not_false_eq_true]
  · intro entry edges depth free term
    rw [meaning]
    constructor
    · rintro ⟨⟨edge, member⟩, accepted⟩
      exact ⟨edge, member, (edgeMeaning_all holds environment edge term).mp accepted⟩
    · rintro ⟨edge, member, accepted⟩
      exact ⟨⟨edge, member⟩, (edgeMeaning_all holds environment edge term).mpr accepted⟩
  · intro entry members depth free term
    rw [meaning]
    constructor
    · rintro ⟨⟨member, present⟩, accepted⟩
      exact ⟨member, present, accepted⟩
    · rintro ⟨member, present, accepted⟩
      exact ⟨⟨member, present⟩, accepted⟩

end MicroCFTA.InternedGuardedLanguage
