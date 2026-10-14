import MicroCFTA.BinderLanguage

/-!
# Least languages with a Mu-unfolding budget

The budget bounds binder steps on each accepting path. Larger budgets retain
accepted terms. A binder consumes one step before its body. Constructor
steps do not consume this budget. This budget is separate from term rank.
-/
namespace MicroCFTA.BinderBudgetLanguage
open Language

/-- A budget language assigns accepted finite terms to each unfolding bound. -/
abbrev Lang (Symbol : Type) := Nat → Term Symbol → Prop

/-- Inclusion retains each accepted term at its original unfolding bound. -/
def Included (left right : Lang Symbol) : Prop := ∀ budget term, left budget term → right budget term

/-- Increasing the unfolding bound cannot remove an accepted term. -/
def Upward (language : Lang Symbol) : Prop :=
  ∀ before after, before ≤ after → ∀ term, language before term → language after term

/-- A body transformer retains inclusion at every unfolding bound. -/
def Monotone (transform : Lang Symbol → Lang Symbol) : Prop :=
  ∀ before after, Included before after → Included (transform before) (transform after)

/-- Intersect the upward languages closed under the body transformer. -/
def least (transform : Lang Symbol → Lang Symbol) : Lang Symbol :=
  fun budget term => ∀ candidate, Upward candidate → Included (transform candidate) candidate → candidate budget term

/-- The least budget language is upward because every candidate language is upward. -/
theorem least_upward (transform : Lang Symbol → Lang Symbol) : Upward (least transform) := by
  intro before after bounded term accepted candidate upward closed
  exact upward before after bounded term (accepted candidate upward closed)

/-- The least language is included in every upward closed candidate. -/
theorem least_le (transform : Lang Symbol → Lang Symbol) (candidate : Lang Symbol)
    (upward : Upward candidate) (closed : Included (transform candidate) candidate) : Included (least transform) candidate :=
  fun _ _ accepted => accepted candidate upward closed

/-- Pointwise body inclusion retains least-language inclusion. -/
theorem least_mono (left right : Lang Symbol → Lang Symbol)
    (included : ∀ candidate, Included (left candidate) (right candidate)) : Included (least left) (least right) := by
  intro budget term accepted candidate upward closed
  exact accepted candidate upward (fun bound term body => closed bound term (included candidate bound term body))

/-- Equal body transformers have equal least budget languages. -/
theorem least_congr (left right : Lang Symbol → Lang Symbol)
    (same : ∀ candidate budget term, left candidate budget term ↔ right candidate budget term) : least left = least right := by
  funext budget term
  apply propext
  exact ⟨least_mono left right (fun candidate budget term => (same candidate budget term).mp) budget term,
    least_mono right left (fun candidate budget term => (same candidate budget term).mpr) budget term⟩

/-- A positive body cannot add a term outside the least budget language. -/
theorem least_closed (transform : Lang Symbol → Lang Symbol) (monotone : Monotone transform) :
    Included (transform (least transform)) (least transform) := by
  intro budget term accepted candidate upward closed
  exact closed budget term (monotone _ _ (least_le transform candidate upward closed) budget term accepted)

/-- An upward positive body exposes the least language in one body step. -/
theorem least_unfold (transform : Lang Symbol → Lang Symbol) (monotone : Monotone transform)
    (upward : Upward (transform (least transform))) : Included (least transform) (transform (least transform)) :=
  least_le transform _ upward (monotone _ _ (least_closed transform monotone))

/-- A binder step supplies a strictly smaller unfolding bound to its body. -/
def shift (language : Lang Symbol) : Lang Symbol :=
  fun budget term => ∃ smaller, smaller < budget ∧ language smaller term

/-- Every shifted language is upward, even before any body monotonicity proof. -/
theorem shift_upward (language : Lang Symbol) : Upward (shift language) := by
  intro before after bounded term accepted
  obtain ⟨smaller, less, accepted⟩ := accepted
  exact ⟨smaller, Nat.lt_of_lt_of_le less bounded, accepted⟩

/-- A binder step retains inclusion of body languages. -/
theorem shift_mono (left right : Lang Symbol) (included : Included left right) : Included (shift left) (shift right) := by
  rintro budget term ⟨smaller, less, accepted⟩
  exact ⟨smaller, less, included smaller term accepted⟩

/-- Interpret a recursive binder with one unfolding step for each body visit. -/
def mu (body : Lang Symbol → Lang Symbol) : Lang Symbol := least (fun candidate => shift (body candidate))

/-- Every budgeted binder language retains its terms at larger bounds. -/
theorem mu_upward (body : Lang Symbol → Lang Symbol) : Upward (mu body) := least_upward _

/-- Increasing every body result retains every budgeted binder result. -/
theorem mu_mono (left right : Lang Symbol → Lang Symbol) (included : ∀ candidate, Included (left candidate) (right candidate)) :
    Included (mu left) (mu right) := least_mono _ _ (fun candidate => shift_mono _ _ (included candidate))

/-- A positive binder accepts exactly one body derivation at a strictly smaller unfolding bound. -/
theorem mu_unfold (body : Lang Symbol → Lang Symbol) (monotone : Monotone body) (budget : Nat) (term : Term Symbol) :
    mu body budget term ↔ ∃ smaller, smaller < budget ∧ body (mu body) smaller term := by
  have positive : Monotone (fun candidate => shift (body candidate)) :=
    fun before after included => shift_mono _ _ (monotone before after included)
  exact ⟨least_unfold _ positive (shift_upward _) budget term, least_closed _ positive budget term⟩

/-- Zero unfolding budget cannot accept a binder term. -/
theorem mu_zero (body : Lang Symbol → Lang Symbol) (monotone : Monotone body) (term : Term Symbol) : ¬ mu body 0 term := by
  intro accepted
  obtain ⟨smaller, impossible, _⟩ := (mu_unfold body monotone 0 term).mp accepted
  omega

/-- A constant raw binder still consumes one unfolding step. -/
theorem mu_constant (language : Lang Symbol) : mu (fun _ => language) = shift language := by
  funext budget term
  exact propext (mu_unfold _ (fun _ _ _ _ _ accepted => accepted) budget term)

/-- A bare recursive self body has no accepted finite term at any unfolding bound. -/
theorem mu_self : mu (fun language : Lang Symbol => language) = fun _ _ => False := by
  funext budget term
  apply propext
  constructor
  · intro accepted
    exact accepted (fun _ _ => False) (fun _ _ _ _ impossible => impossible) (by
      rintro bound term ⟨smaller, less, impossible⟩
      exact impossible)
  · intro impossible; exact impossible.elim

/-- A direct self alternative cannot enlarge an upward closed binder candidate. -/
theorem self_alternative_closed (candidate language : Lang Symbol) (upward : Upward candidate) :
    Included (shift (fun budget term => candidate budget term ∨ language budget term)) candidate ↔
      Included (shift language) candidate := by
  constructor
  · intro closed budget term accepted
    obtain ⟨smaller, less, accepted⟩ := accepted
    exact closed budget term ⟨smaller, less, Or.inr accepted⟩
  · rintro closed budget term ⟨smaller, less, accepted | accepted⟩
    · exact upward smaller budget (Nat.le_of_lt less) term accepted
    · exact closed budget term ⟨smaller, less, accepted⟩

/-- Removing direct self alternatives retains the complete budgeted least language. -/
theorem mu_self_alternative (body : Lang Symbol → Lang Symbol) :
    mu (fun candidate budget term => candidate budget term ∨ body candidate budget term) = mu body := by
  funext budget term
  apply propext
  constructor
  · intro accepted candidate upward closed
    exact accepted candidate upward ((self_alternative_closed candidate (body candidate) upward).mpr closed)
  · intro accepted candidate upward closed
    exact accepted candidate upward ((self_alternative_closed candidate (body candidate) upward).mp closed)

end MicroCFTA.BinderBudgetLanguage
