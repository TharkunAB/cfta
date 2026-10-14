import MicroCFTA.InternedGuardedSmartBudgetSyntaxSupport

/-!
# Literal roots and deep budget dependencies

Literal root alternatives enter the language at the same bound. If ambient
languages agree on deep names, a changed accepted term must come from a
literal root. The existing shapes retain both sets separately.
-/
namespace MicroCFTA.InternedGuardedSmartBudgetSupport
open Language InternedDepthSemantics
open BinderBudgetLanguage (Lang Included)

/-- Every literal root alternative enters the budget language at the same bound. -/
def Lower (environment : Atom → Lang Symbol) (shape : Shape Atom) (language : Lang Symbol) : Prop :=
  Included (roots environment shape.roots) language

/-- Root inclusion and deep dependency extend the existing complete support relation. -/
structure DeepRelated (shape : Shape Atom) (before after : Atom → Lang Symbol) (left right : Lang Symbol) : Prop
    extends Related shape before after left right where
  root_left : Lower before shape left
  root_right : Lower after shape right
  deep_change : Agree before after shape.deep →
    Included left (fun budget term => right budget term ∨ roots before shape.roots budget term)

/-- A shape without roots has no literal alternatives and needs only its complete support law. -/
theorem deep_rootless (shape : Shape Atom) (before after : Atom → Lang Symbol) (left right : Lang Symbol)
    (related : Related shape before after left right) (rootless : shape.roots = []) :
    DeepRelated shape before after left right := by
  refine ⟨related, ?_, ?_, ?_⟩
  · rintro budget term ⟨name, member, _⟩; rw [rootless] at member; cases member
  · rintro budget term ⟨name, member, _⟩; rw [rootless] at member; cases member
  · intro agree budget term accepted
    left
    have same := related.support (fun name member => agree name (by simpa only [Shape.free, rootless, List.nil_append] using member))
    exact same ▸ accepted

/-- Equal input languages satisfy deep support when their root bounds agree. -/
theorem deep_self (environment : Atom → Lang Symbol) (shape : Shape Atom) (language : Lang Symbol)
    (upper : Upper environment shape language) (lower : Lower environment shape language) :
    DeepRelated shape environment environment language language :=
  ⟨⟨upper, upper, fun _ => rfl⟩, lower, lower, fun _ _ _ accepted => Or.inl accepted⟩

/-- A symbolic local has its exact literal root and no deep dependency. -/
theorem deep_local (before after : Atom → Lang Symbol) (left right : Lang Symbol) :
    DeepRelated ⟨[Sum.inl ()], [], false, 0⟩ (extend before left) (extend after right) left right := by
  refine ⟨related_local before after left right, ?_, ?_, ?_⟩
  · rintro budget term ⟨name, member, accepted⟩
    simp only [List.mem_singleton] at member
    subst name
    exact accepted
  · rintro budget term ⟨name, member, accepted⟩
    simp only [List.mem_singleton] at member
    subst name
    exact accepted
  · intro _ budget term accepted
    exact Or.inr ⟨.inl (), by simp, accepted⟩

/-- Lifting an external capture retains its literal roots and deep budget support. -/
theorem deep_lift (before after : Atom → Lang Symbol) (leftCandidate rightCandidate : Lang Symbol)
    (shape : Shape Atom) (left right : Lang Symbol) (related : DeepRelated shape before after left right) :
    DeepRelated (shape.map Sum.inr) (extend before leftCandidate) (extend after rightCandidate) left right := by
  refine ⟨related_lift before after leftCandidate rightCandidate shape left right related.toRelated, ?_, ?_, ?_⟩
  · rintro budget term ⟨name, member, accepted⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact related.root_left budget term ⟨original, present, accepted⟩
  · rintro budget term ⟨name, member, accepted⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact related.root_right budget term ⟨original, present, accepted⟩
  · intro agree budget term accepted
    have beforeAgree : Agree before after shape.deep := by
      intro name member
      exact agree (.inr name) (List.mem_map.mpr ⟨name, member, rfl⟩)
    rcases related.deep_change beforeAgree budget term accepted with accepted | ⟨name, member, accepted⟩
    · exact Or.inl accepted
    · exact Or.inr ⟨.inr name, List.mem_map.mpr ⟨name, member, rfl⟩, accepted⟩

/-- Removing the symbolic local retains every external literal root alternative. -/
theorem lower_roots (environment : Atom → Lang Symbol) (shape : Shape (Sum Unit Atom))
    (language : Lang Symbol) (bound : Lower (extend environment (fun _ _ => False)) shape language) :
    Lower environment ⟨lower shape.roots, lower shape.deep, shape.hasOpaque, shape.depth⟩ language := by
  rintro budget term ⟨name, member, accepted⟩
  apply bound budget term
  exact ⟨.inr name, (InternedFreeNameSemantics.lower_member shape.roots name).mp member, accepted⟩

/-- Both smart binder branches retain literal root inclusion and deep dependency. -/
theorem deep_binder (before after : Atom → Lang Symbol) (smart : Bool) (shape : Shape (Sum Unit Atom))
    (left right : Lang Symbol → Lang Symbol)
    (body : ∀ leftCandidate rightCandidate,
      DeepRelated shape (extend before leftCandidate) (extend after rightCandidate) (left leftCandidate) (right rightCandidate)) :
    DeepRelated (binder smart shape) before after
      (if !smart || hasLocal shape.deep then BinderBudgetLanguage.mu left else left (fun _ _ => False))
      (if !smart || hasLocal shape.deep then BinderBudgetLanguage.mu right else right (fun _ _ => False)) := by
  have base := related_binder before after smart shape left right (fun first second => (body first second).toRelated)
  by_cases keep : (!smart || hasLocal shape.deep) = true
  · apply deep_rootless _ _ _ _ _ base
    simp only [binder, keep, ↓reduceIte]
  · refine ⟨base, ?_, ?_, ?_⟩
    · simpa only [binder, keep, Bool.false_eq_true, ↓reduceIte] using
        lower_roots before shape _ (body (fun _ _ => False) (fun _ _ => False)).root_left
    · simpa only [binder, keep, Bool.false_eq_true, ↓reduceIte] using
        lower_roots after shape _ (body (fun _ _ => False) (fun _ _ => False)).root_right
    · intro agree budget term accepted
      have bodyAgree : Agree (extend before (fun _ _ => False)) (extend after (fun _ _ => False)) shape.deep := by
        intro name member
        cases name with
        | inl token => rfl
        | inr name =>
            apply agree name
            simp only [binder, keep, Bool.false_eq_true, ↓reduceIte]
            exact (InternedFreeNameSemantics.lower_member shape.deep name).mpr member
      have current : left (fun _ _ => False) budget term := by simpa only [keep, Bool.false_eq_true, ↓reduceIte] using accepted
      rcases (body (fun _ _ => False) (fun _ _ => False)).deep_change bodyAgree budget term current with accepted | ⟨name, member, accepted⟩
      · exact Or.inl (by simpa only [keep, Bool.false_eq_true, ↓reduceIte] using accepted)
      · right
        cases name with
        | inl token => exact accepted.elim
        | inr name =>
            refine ⟨name, ?_, accepted⟩
            simp only [binder, keep, Bool.false_eq_true, ↓reduceIte]
            exact (InternedFreeNameSemantics.lower_member shape.roots name).mpr member

end MicroCFTA.InternedGuardedSmartBudgetSupport
