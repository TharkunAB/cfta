import MicroCFTA.InternedNodeIdentityFootprint

/-!
# Old outputs from newly allocated recursive records

A raw recursive result exposes its own entry identity. Smart cleanup can
hide a new entry only by returning an unused body or removing a bare self
reference. This classification uses the actual source cleanup branches.
-/
namespace MicroCFTA.InternedCleanupAge
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedNodeIdentityFootprint
open InternedBinderProtocol (NodeKey)

/-- The recursive record itself contains its exact allocated identity. -/
theorem mu_occurs (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
    Occurs entry.identity (.mu entry body depth ordinary) :=
  .entry (.mu entry body depth ordinary) entry rfl rfl

/-- A reference-shaped identity determines the exact complete reference value. -/
theorem reference_eq (value : Value Symbol Guard) (name : InternedBinderProtocol.Reference)
    (same : value.referenceOf = .ref name) : value = .reference name := by
  cases value <;> simp_all [Value.referenceOf]

/-- An old output can hide a new recursive entry only in the two smart cleanup branches. -/
theorem finish_old_cases (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (cutoff : Nat) (fresh : cutoff ≤ entry.identity)
    (old : ∀ identity, Occurs identity (finish smart (.mu entry body depth ordinary)) → identity < cutoff) :
    smart = true ∧
      ((finish smart (.mu entry body depth ordinary) = body ∧ .interned entry.identity ∉ body.free) ∨
        (finish smart (.mu entry body depth ordinary) = .empty ∧ body = .reference (.interned entry.identity))) := by
  cases smart with
  | false =>
      have impossible := old entry.identity (mu_occurs entry body depth ordinary)
      omega
  | true =>
      refine ⟨rfl, ?_⟩
      by_cases unused : .interned entry.identity ∉ body.free
      · exact Or.inl ⟨by simp [finish, cleanup, unused], unused⟩
      · by_cases self : body.referenceOf = .ref (.interned entry.identity)
        · exact Or.inr ⟨by simp only [finish, cleanup, unused, self, ↓reduceIte], reference_eq body _ self⟩
        · have same : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
            simp only [finish, cleanup, unused, self, ↓reduceIte]
          have impossible := old entry.identity (same.symm ▸ mu_occurs entry body depth ordinary)
          omega

/-- Complete old output footprints are exactly unused old bodies or removed self references. -/
theorem finish_old_iff (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (cutoff : Nat) (fresh : cutoff ≤ entry.identity) :
    (∀ identity, Occurs identity (finish smart (.mu entry body depth ordinary)) → identity < cutoff) ↔
      smart = true ∧
        ((.interned entry.identity ∉ body.free ∧ (∀ identity, Occurs identity body → identity < cutoff)) ∨
          body = .reference (.interned entry.identity)) := by
  constructor
  · intro old
    obtain ⟨smartEq, cases⟩ := finish_old_cases smart entry body depth ordinary cutoff fresh old
    refine ⟨smartEq, ?_⟩
    rcases cases with ⟨same, unused⟩ | ⟨_, self⟩
    · exact Or.inl ⟨unused, fun identity occurrence => old identity (same.symm ▸ occurrence)⟩
    · exact Or.inr self
  · rintro ⟨rfl, unused | rfl⟩
    · simpa [finish, cleanup, unused.1] using unused.2
    · intro identity occurrence
      have empty : finish true (.mu entry (.reference (.interned entry.identity)) depth ordinary) = .empty := by
        simp [finish, cleanup, Value.free, Value.referenceOf]
      rw [empty] at occurrence
      cases occurrence with
      | entry _ record present _ => cases present
      | child _ child member _ => cases member

end MicroCFTA.InternedCleanupAge
