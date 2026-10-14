import MicroCFTA.InternedGuardedSmartBudget
import MicroCFTA.InternedDepthFreeProjection

/-!
# Budget language support from existing depth shapes

Pure root alternatives bound accepted terms at each unfolding budget.
Complete free names bound ambient changes at all budgets. The actual smart
decision either retains a Mu step or supplies an empty local language.
-/
namespace MicroCFTA.InternedGuardedSmartBudgetSupport
open Language InternedDepthSemantics
open BinderBudgetLanguage (Lang Included)

/-- Interpret the listed root alternatives at every unfolding bound. -/
def roots (environment : Atom → Lang Symbol) (names : List Atom) : Lang Symbol :=
  fun budget term => ∃ name ∈ names, environment name budget term

/-- A shape without an opaque alternative bounds its language by its literal roots. -/
def Upper (environment : Atom → Lang Symbol) (shape : Shape Atom) (language : Lang Symbol) : Prop :=
  shape.hasOpaque = false → Included language (roots environment shape.roots)

/-- Ambient budget languages agree completely on each stated free name. -/
def Agree (before after : Atom → Lang Symbol) (names : List Atom) : Prop :=
  ∀ name ∈ names, before name = after name

/-- The existing shape bounds both budget languages and their ambient dependencies. -/
structure Related (shape : Shape Atom) (before after : Atom → Lang Symbol) (left right : Lang Symbol) : Prop where
  upper_left : Upper before shape left
  upper_right : Upper after shape right
  support : Agree before after shape.free → left = right

/-- Empty syntax accepts no term and reads no ambient name. -/
theorem related_empty (before after : Atom → Lang Symbol) :
    Related {} before after (fun _ _ => False) (fun _ _ => False) :=
  ⟨fun _ _ _ impossible => impossible.elim, fun _ _ _ impossible => impossible.elim, fun _ => rfl⟩

/-- Shape union retains both operand root bounds. -/
theorem upper_combine (environment : Atom → Lang Symbol) (first second : Shape Atom)
    (left right : Lang Symbol) (leftBound : Upper environment first left) (rightBound : Upper environment second right) :
    Upper environment (combine first second) (fun budget term => left budget term ∨ right budget term) := by
  intro nonopaque budget term accepted
  have flags : first.hasOpaque = false ∧ second.hasOpaque = false := by simpa only [combine, Bool.or_eq_false_iff] using nonopaque
  rcases accepted with accepted | accepted
  · obtain ⟨name, member, accepted⟩ := leftBound flags.1 budget term accepted
    exact ⟨name, List.mem_append_left _ member, accepted⟩
  · obtain ⟨name, member, accepted⟩ := rightBound flags.2 budget term accepted
    exact ⟨name, List.mem_append_right _ member, accepted⟩

/-- Two source alternatives retain the complete budget support relation. -/
theorem related_combine (before after : Atom → Lang Symbol) (first second : Shape Atom)
    (leftFirst rightFirst leftSecond rightSecond : Lang Symbol)
    (firstRelated : Related first before after leftFirst rightFirst)
    (secondRelated : Related second before after leftSecond rightSecond) :
    Related (combine first second) before after
      (fun budget term => leftFirst budget term ∨ leftSecond budget term)
      (fun budget term => rightFirst budget term ∨ rightSecond budget term) := by
  refine ⟨upper_combine _ _ _ _ _ firstRelated.upper_left secondRelated.upper_left,
    upper_combine _ _ _ _ _ firstRelated.upper_right secondRelated.upper_right, ?_⟩
  intro agree
  rw [firstRelated.support (fun name member => agree name ((InternedDepthFreeProjection.combine_member first second name).mpr (Or.inl member))),
    secondRelated.support (fun name member => agree name ((InternedDepthFreeProjection.combine_member first second name).mpr (Or.inr member)))]

/-- A symbolic local receives its budget language while captures retain their ambient inputs. -/
def extend (environment : Atom → Lang Symbol) (language : Lang Symbol) : Sum Unit Atom → Lang Symbol
  | .inl _ => language
  | .inr name => environment name

/-- Lifting a capture retains its root bound under any symbolic local budget language. -/
theorem upper_lift (environment : Atom → Lang Symbol) (candidate language : Lang Symbol)
    (shape : Shape Atom) (bound : Upper environment shape language) :
    Upper (extend environment candidate) (shape.map Sum.inr) language := by
  intro nonopaque budget term accepted
  obtain ⟨name, member, accepted⟩ := bound nonopaque budget term accepted
  exact ⟨.inr name, List.mem_map.mpr ⟨name, member, rfl⟩, accepted⟩

/-- A lifted capture retains budget support for its mapped free names. -/
theorem related_lift (before after : Atom → Lang Symbol) (leftCandidate rightCandidate : Lang Symbol)
    (shape : Shape Atom) (left right : Lang Symbol) (related : Related shape before after left right) :
    Related (shape.map Sum.inr) (extend before leftCandidate) (extend after rightCandidate) left right := by
  refine ⟨upper_lift _ _ _ _ related.upper_left, upper_lift _ _ _ _ related.upper_right, ?_⟩
  intro agree
  apply related.support
  intro name member
  exact agree (.inr name) (by rw [InternedDepthFreeProjection.map_free]; exact List.mem_map.mpr ⟨name, member, rfl⟩)

/-- A new local has exactly its supplied budget language and one literal root. -/
theorem related_local (before after : Atom → Lang Symbol) (left right : Lang Symbol) :
    Related ⟨[Sum.inl ()], [], false, 0⟩ (extend before left) (extend after right) left right := by
  refine ⟨fun _ budget term accepted => ⟨.inl (), by simp, accepted⟩,
    fun _ budget term accepted => ⟨.inl (), by simp, accepted⟩, ?_⟩
  intro agree
  exact agree (.inl ()) (by simp [Shape.free])

/-- The empty-local branch removes every local root from its root bound. -/
theorem lower_empty (environment : Atom → Lang Symbol) (body : Shape (Sum Unit Atom))
    (language : Lang Symbol) (bound : Upper (extend environment (fun _ _ => False)) body language) :
    Upper environment ⟨lower body.roots, lower body.deep, body.hasOpaque, body.depth⟩ language := by
  intro nonopaque budget term accepted
  obtain ⟨name, member, accepted⟩ := bound nonopaque budget term accepted
  cases name with
  | inl token => exact accepted.elim
  | inr name => exact ⟨name, (InternedFreeNameSemantics.lower_member body.roots name).mpr member, accepted⟩

/-- The existing smart decision retains root bounds and complete ambient budget support. -/
theorem related_binder (before after : Atom → Lang Symbol) (smart : Bool) (shape : Shape (Sum Unit Atom))
    (left right : Lang Symbol → Lang Symbol)
    (body : ∀ leftCandidate rightCandidate,
      Related shape (extend before leftCandidate) (extend after rightCandidate) (left leftCandidate) (right rightCandidate)) :
    Related (binder smart shape) before after
      (if !smart || hasLocal shape.deep then BinderBudgetLanguage.mu left else left (fun _ _ => False))
      (if !smart || hasLocal shape.deep then BinderBudgetLanguage.mu right else right (fun _ _ => False)) := by
  have supported (candidate : Lang Symbol) (agree : Agree before after (binder smart shape).free) : left candidate = right candidate := by
    apply (body candidate candidate).support
    intro name member
    cases name with
    | inl token => rfl
    | inr name =>
        apply agree name
        rw [InternedDepthFreeProjection.binder_free]
        exact (InternedFreeNameSemantics.lower_member shape.free name).mpr member
  rw [binder]
  split <;> rename_i decision
  · refine ⟨?_, ?_, ?_⟩
    · intro impossible; contradiction
    · intro impossible; contradiction
    · intro agree
      apply congrArg BinderBudgetLanguage.mu
      funext candidate
      apply supported candidate
      simpa only [binder, decision, ↓reduceIte] using agree
  · refine ⟨lower_empty before shape _ (body (fun _ _ => False) (fun _ _ => False)).upper_left,
      lower_empty after shape _ (body (fun _ _ => False) (fun _ _ => False)).upper_right, ?_⟩
    intro agree
    apply supported (fun _ _ => False)
    simpa only [binder, decision, Bool.false_eq_true, ↓reduceIte] using agree

end MicroCFTA.InternedGuardedSmartBudgetSupport
