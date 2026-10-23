import MicroCFTA.IntersectCompleteness

/-!
# Independent finite input derivations

These derivations use only input payloads. They do not mention intersection.
The rank bounds binder unfolding along each branch. Recursive occurrences
and their binders have the same language and the same derivation ranks.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

mutual
/-- A finite source input derivation with an explicit binder-unfolding bound. -/
inductive InputDerivation (view : View Symbol) : Input → Nat → Term Symbol → Prop where
  | node (row : Row Symbol) (member : row ∈ view.rows name) (terms : List (Term Symbol))
      (children : InputForestDerivation view rank row.children terms)
      (guard : row.guard (.node row.label terms) = true) :
      InputDerivation view (.node name) rank (.node row.label terms)
  | binder (body : InputDerivation view (view.body name) smaller term) (less : smaller < rank) :
      InputDerivation view (.mu name) rank term
  | reference (body : InputDerivation view (view.body name) smaller term) (less : smaller < rank) :
      InputDerivation view (.ref name) rank term
  | union (member : child ∈ view.members name) (body : InputDerivation view child smaller term) (less : smaller ≤ rank) :
      InputDerivation view (.union name) rank term

/-- Ordered child derivations share an upper bound on binder unfolding. -/
inductive InputForestDerivation (view : View Symbol) : Nat → List Input → List (Term Symbol) → Prop where
  | nil : InputForestDerivation view rank [] []
  | cons (head : InputDerivation view child smaller term) (bounded : smaller ≤ rank)
      (tail : InputForestDerivation view rank children terms) :
      InputForestDerivation view rank (child :: children) (term :: terms)
end

/-- The mutual forest relation contains exactly the bounded ordered child derivations. -/
theorem input_forest_exact (view : View Symbol) (rank : Nat) (children : List Input) (terms : List (Term Symbol)) :
    InputForestDerivation view rank children terms ↔
      All₂ (fun child term => ∃ smaller, smaller ≤ rank ∧ InputDerivation view child smaller term) children terms := by
  constructor
  · intro accepted
    induction children generalizing terms with
    | nil => cases accepted; exact .nil
    | cons child children ih =>
      cases accepted with
      | cons head bounded tail => exact .cons ⟨_, bounded, head⟩ (ih _ tail)
  · intro accepted
    induction accepted with
    | nil => exact .nil
    | cons head tail ih => obtain ⟨smaller, bounded, derivation⟩ := head; exact .cons derivation bounded ih

/-- Increasing a bound preserves the same finite input derivation. -/
theorem input_derivation_mono (view : View Symbol) (input : Input) (before after : Nat)
    (bounded : before ≤ after) (term : Term Symbol) (accepted : InputDerivation view input before term) :
    InputDerivation view input after term := by
  cases accepted with
  | node row member terms children guard =>
    exact .node row member terms
      ((input_forest_exact view after _ _).mpr
        (All₂.imp (fun _ _ ⟨rank, smaller, derivation⟩ => ⟨rank, Nat.le_trans smaller bounded, derivation⟩)
          ((input_forest_exact view before _ _).mp children))) guard
  | binder body less => exact .binder body (Nat.lt_of_lt_of_le less bounded)
  | reference body less => exact .reference body (Nat.lt_of_lt_of_le less bounded)
  | union member body less => exact .union member body (Nat.le_trans less bounded)

/-- A recursive occurrence has exactly its binder's finite derivations. -/
theorem input_derivation_reference (view : View Symbol) (name rank : Nat) (term : Term Symbol) :
    InputDerivation view (.ref name) rank term ↔ InputDerivation view (.mu name) rank term := by
  constructor
  · intro accepted; cases accepted with | reference body less => exact .binder body less
  · intro accepted; cases accepted with | binder body less => exact .reference body less

/-- The binder tag is the canonical representative of a recursive identity. -/
def inputRepresentative : Input → Input
  | .ref name => .mu name
  | input => input

/-- Valid payloads and canonical identities give independent least input semantics. -/
structure FiniteInput (view : View Symbol) where
  valid : Input → Prop
  representative : Nat → Input
  identity_exact : ∀ input, valid input → input ≠ .empty → representative (identity input) = inputRepresentative input
  body_valid : ∀ name, valid (.mu name) → valid (view.body name)
  reference_valid : ∀ name, valid (.ref name) → valid (.mu name)
  row_valid : ∀ name, valid (.node name) → ∀ row ∈ view.rows name, ∀ child ∈ row.children, valid child
  union_valid : ∀ name, valid (.union name) → ∀ child ∈ view.members name, valid child
  copy_exact : ∀ input, valid input → closed view input = true → ∀ environment,
    meaning environment (view.copy input) = fun term => ∃ rank, InputDerivation view input rank term

/-- Identity-indexed input ranks contain only independent finite derivations. -/
def finiteRanks (view : View Symbol) (inputs : FiniteInput view) (name rank : Nat) : Lang Symbol :=
  InputDerivation view (inputs.representative name) rank

/-- Canonical lookup retains each valid input's complete finite derivations. -/
theorem finiteRanks_exact (view : View Symbol) (inputs : FiniteInput view) (input : Input)
    (valid : inputs.valid input) (rank : Nat) (term : Term Symbol) :
    inputAt (finiteRanks view inputs) input rank term ↔ InputDerivation view input rank term := by
  cases input with
  | empty => constructor <;> intro accepted <;> cases accepted
  | node name =>
    have same := inputs.identity_exact (.node name) valid (by intro h; cases h)
    simp only [identity, inputRepresentative] at same
    simpa only [inputAt, inputLanguage, identity, finiteRanks, inputRepresentative] using
      (show InputDerivation view (inputs.representative name) rank term ↔ InputDerivation view (.node name) rank term by rw [same])
  | mu name =>
    have same := inputs.identity_exact (.mu name) valid (by intro h; cases h)
    simp only [identity, inputRepresentative] at same
    simpa only [inputAt, inputLanguage, identity, finiteRanks, inputRepresentative] using
      (show InputDerivation view (inputs.representative name) rank term ↔ InputDerivation view (.mu name) rank term by rw [same])
  | union name =>
    have same := inputs.identity_exact (.union name) valid (by intro h; cases h)
    simp only [identity, inputRepresentative] at same
    simpa only [inputAt, inputLanguage, identity, finiteRanks, inputRepresentative] using
      (show InputDerivation view (inputs.representative name) rank term ↔ InputDerivation view (.union name) rank term by rw [same])
  | ref name =>
    have same := inputs.identity_exact (.ref name) valid (by intro h; cases h)
    simp only [inputAt, inputLanguage, identity, finiteRanks, show inputs.representative name = .mu name from same]
    exact (input_derivation_reference view name rank term).symm

/-- Erasing the bound gives the independent least finite input language. -/
def finiteLanguages (view : View Symbol) (inputs : FiniteInput view) (name : Nat) : Lang Symbol :=
  fun term => ∃ rank, finiteRanks view inputs name rank term

/-- A valid input's identity language is exactly its finite derivation language. -/
theorem finiteLanguages_exact (view : View Symbol) (inputs : FiniteInput view) (input : Input)
    (valid : inputs.valid input) (term : Term Symbol) :
    inputLanguage (finiteLanguages view inputs) input term ↔ ∃ rank, InputDerivation view input rank term := by
  have ranks : inputLanguage (finiteLanguages view inputs) input term ↔
      ∃ rank, inputAt (finiteRanks view inputs) input rank term := by
    cases input <;> simp [inputLanguage, inputAt, finiteLanguages]
  rw [ranks]
  exact exists_congr fun rank => finiteRanks_exact view inputs input valid rank term

/-- Finitely many child derivations have a common upper bound. -/
theorem input_forest_bound (view : View Symbol) (children : List Input) (terms : List (Term Symbol))
    (accepted : All₂ (fun child term => ∃ rank, InputDerivation view child rank term) children terms) :
    ∃ bound, All₂ (fun child term => ∃ rank, rank ≤ bound ∧ InputDerivation view child rank term) children terms := by
  induction accepted with
  | nil => exact ⟨0, .nil⟩
  | cons head tail ih =>
    obtain ⟨first, head⟩ := head
    obtain ⟨rest, tail⟩ := ih
    exact ⟨max first rest, .cons ⟨first, Nat.le_max_left _ _, head⟩
      (All₂.imp (fun _ _ ⟨rank, bounded, derivation⟩ =>
        ⟨rank, Nat.le_trans bounded (Nat.le_max_right _ _), derivation⟩) tail)⟩

/-- Erasing derivation bounds preserves the binder's defining language equation. -/
theorem input_binder_exact (view : View Symbol) (name : Nat) (term : Term Symbol) :
    (∃ rank, InputDerivation view (.mu name) rank term) ↔
      ∃ rank, InputDerivation view (view.body name) rank term := by
  constructor
  · rintro ⟨rank, accepted⟩
    cases accepted with
    | binder body _ => exact ⟨_, body⟩
  · rintro ⟨rank, accepted⟩
    exact ⟨rank + 1, .binder accepted (by omega)⟩

/-- Erasing derivation bounds preserves every constructor row and child position. -/
theorem input_node_exact (view : View Symbol) (name : Nat) (term : Term Symbol) :
    (∃ rank, InputDerivation view (.node name) rank term) ↔
      ∃ row ∈ view.rows name, ∃ terms, term = .node row.label terms ∧
        All₂ (fun child term => ∃ rank, InputDerivation view child rank term) row.children terms ∧ row.guard term = true := by
  constructor
  · rintro ⟨rank, accepted⟩
    cases accepted with
    | node row member terms children guard =>
      exact ⟨row, member, terms, rfl,
        All₂.imp (fun _ _ ⟨rank, _, derivation⟩ => ⟨rank, derivation⟩)
          ((input_forest_exact view rank _ _).mp children), guard⟩
  · rintro ⟨row, member, terms, rfl, children, guard⟩
    obtain ⟨rank, children⟩ := input_forest_bound view row.children terms children
    exact ⟨rank, .node row member terms ((input_forest_exact view rank _ _).mpr children) guard⟩

/-- An epsilon union adds no constructor to an independent input derivation. -/
theorem input_union_exact (view : View Symbol) (name : Nat) (term : Term Symbol) :
    (∃ rank, InputDerivation view (.union name) rank term) ↔
      ∃ child ∈ view.members name, ∃ rank, InputDerivation view child rank term := by
  constructor
  · rintro ⟨rank, accepted⟩
    cases accepted with
    | union member body _ => exact ⟨_, member, _, body⟩
  · rintro ⟨child, member, rank, accepted⟩
    exact ⟨rank, .union member accepted (Nat.le_refl _)⟩

/-- Independent finite derivations satisfy the input equations used by soundness. -/
def finiteInputMeaning (view : View Symbol) (inputs : FiniteInput view) : InputMeaning view where
  valid := inputs.valid
  languages := finiteLanguages view inputs
  body_valid := inputs.body_valid
  body_exact := by
    intro name valid
    funext term
    apply propext
    change inputLanguage (finiteLanguages view inputs) (.mu name) term ↔ _
    rw [finiteLanguages_exact view inputs (.mu name) valid, input_binder_exact,
      finiteLanguages_exact view inputs (view.body name) (inputs.body_valid name valid)]
  reference_valid := inputs.reference_valid
  row_valid := inputs.row_valid
  row_exact := by
    intro name valid term
    change inputLanguage (finiteLanguages view inputs) (.node name) term ↔ _
    rw [finiteLanguages_exact view inputs (.node name) valid, input_node_exact]
    constructor
    · rintro ⟨row, member, terms, same, children, guard⟩
      refine ⟨row, member, terms, same, ?_, guard⟩
      exact SymbolicInternedView.all₂_scoped_imp _ _ _ _ children (by
        intro child present output _ accepted
        exact (finiteLanguages_exact view inputs child (inputs.row_valid name valid row member child present) output).mpr accepted)
    · rintro ⟨row, member, terms, same, children, guard⟩
      refine ⟨row, member, terms, same, ?_, guard⟩
      exact SymbolicInternedView.all₂_scoped_imp _ _ _ _ children (by
        intro child present output _ accepted
        exact (finiteLanguages_exact view inputs child (inputs.row_valid name valid row member child present) output).mp accepted)
  union_valid := inputs.union_valid
  union_exact := by
    intro name valid term
    change inputLanguage (finiteLanguages view inputs) (.union name) term ↔ _
    rw [finiteLanguages_exact view inputs (.union name) valid, input_union_exact]
    constructor <;> rintro ⟨child, member, accepted⟩
    · exact ⟨child, member, (finiteLanguages_exact view inputs child (inputs.union_valid name valid child member) term).mpr accepted⟩
    · exact ⟨child, member, (finiteLanguages_exact view inputs child (inputs.union_valid name valid child member) term).mp accepted⟩
  copy_exact := by
    intro input valid isClosed environment
    rw [inputs.copy_exact input valid isClosed environment]
    funext term
    exact propext (finiteLanguages_exact view inputs input valid term).symm

/-- Independent finite derivations satisfy every rank law used by completeness. -/
def finiteRankedInput (view : View Symbol) (inputs : FiniteInput view) : RankedInput view inputs.valid where
  languages := finiteRanks view inputs
  body := by
    intro name valid rank term accepted
    have derivation := (finiteRanks_exact view inputs (.mu name) valid rank term).mp accepted
    cases derivation with
    | binder body less =>
      exact ⟨_, less, (finiteRanks_exact view inputs _ (inputs.body_valid name valid) _ term).mpr body⟩
  row := by
    intro name valid rank term accepted
    have derivation := (finiteRanks_exact view inputs (.node name) valid rank term).mp accepted
    cases derivation with
    | node row member terms children guard =>
      refine ⟨row, member, terms, rfl, ?_, guard⟩
      exact SymbolicInternedView.all₂_scoped_imp _ _ _ _ ((input_forest_exact view rank _ _).mp children) (by
        intro child present output _ accepted
        obtain ⟨smaller, bounded, derivation⟩ := accepted
        exact (finiteRanks_exact view inputs child (inputs.row_valid name valid row member child present) rank output).mpr
          (input_derivation_mono view child smaller rank bounded output derivation))
  union := by
    intro name valid rank term accepted
    have derivation := (finiteRanks_exact view inputs (.union name) valid rank term).mp accepted
    cases derivation with
    | union member body less =>
      exact ⟨_, member, (finiteRanks_exact view inputs _ (inputs.union_valid name valid _ member) rank term).mpr
        (input_derivation_mono view _ _ rank less term body)⟩
  copy := by
    intro input valid isClosed rank term accepted environment
    rw [inputs.copy_exact input valid isClosed environment]
    exact ⟨rank, (finiteRanks_exact view inputs input valid rank term).mp accepted⟩

/-- A successful source schedule computes exactly the common independent finite input derivations. -/
theorem finite_intersection_exact [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (fuel : Nat) (left right : Input) (leftValid : inputs.valid left) (rightValid : inputs.valid right)
    (result : Shape (Payload Symbol)) (completed : run view fuel {} left right = .ok result)
    (environment : Env Symbol) (term : Term Symbol) :
    meaning environment result term ↔
      (∃ rank, InputDerivation view left rank term) ∧ (∃ rank, InputDerivation view right rank term) := by
  have exactResult := top_exact view (finiteInputMeaning view inputs) (finiteRankedInput view inputs)
    (by
      intro input valid term accepted
      obtain ⟨rank, derivation⟩ := (finiteLanguages_exact view inputs input valid term).mp accepted
      exact ⟨rank, (finiteRanks_exact view inputs input valid rank term).mpr derivation⟩)
    fuel left right leftValid rightValid result completed environment term
  simpa only [finiteInputMeaning, finiteLanguages_exact view inputs left leftValid term,
    finiteLanguages_exact view inputs right rightValid term] using exactResult

end MicroCFTA.IntersectSchedule
