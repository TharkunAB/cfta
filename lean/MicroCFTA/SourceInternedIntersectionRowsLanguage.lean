import MicroCFTA.SourceInternedIntersectionRows

/-!
# Exact local language after ordinary intersection construction

The graph reads stored ordinary rows and their ordered child records.
EmptyNode has no run. Canonical interning removes duplicate rows and rows
with an empty child. Neither removal changes this finite-term language.
-/
namespace MicroCFTA.SourceInternedIntersectionRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency Language

/-- Read a plain stored edge without changing its symbol or ordered children. -/
def row (edge : EdgeValue Symbol Unit) : Language.Edge (Value Symbol Unit) Symbol :=
  ⟨edge.entry.key.symbol, edge.children, fun _ => true⟩

/-- The ordinary structural graph has no epsilon or binder transitions. -/
def rows (value : Value Symbol Unit) : List (Language.Edge (Value Symbol Unit) Symbol) :=
  (nodeEdges value).map row

/-- Finite accepted terms of the stored ordinary graph. -/
abbrev Accepts (value : Value Symbol Unit) (term : Term Symbol) := Language.Accepts rows value term

/-- One complete stored edge accepts a term through its ordered child records. -/
def EdgeAccepts (edge : EdgeValue Symbol Unit) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ Accepts edge.children terms

/-- Structural acceptance exposes an actual stored edge, including its literal label. -/
theorem accepts_iff (value : Value Symbol Unit) (term : Term Symbol) :
    Accepts value term ↔ ∃ edge ∈ nodeEdges value, EdgeAccepts edge term := by
  cases term with
  | node symbol terms =>
      simp only [Accepts, Language.accepts_node_iff, rows, List.mem_map]
      constructor
      · rintro ⟨_, ⟨edge, member, rfl⟩, label, runs, _⟩
        exact ⟨edge, member, terms, by rw [← label]; rfl, runs⟩
      · rintro ⟨edge, member, children, same, runs⟩
        cases same
        exact ⟨row edge, ⟨edge, member, rfl⟩, rfl, runs, rfl⟩

/-- EmptyNode has no finite run. -/
theorem empty_rejects (term : Term Symbol) : ¬ Accepts (.empty : Value Symbol Unit) term := by
  rw [accepts_iff]
  simp [nodeEdges]

/-- Successful child runs exclude the source's literal empty-child test. -/
theorem runs_live (values : List (Value Symbol Unit)) (terms : List (Term Symbol))
    (runs : All₂ Accepts values terms) :
    values.any (fun child => child.referenceOf == .empty) = false := by
  induction runs with
  | nil => rfl
  | @cons value term values terms head tail ih =>
      have nonempty : value.referenceOf ≠ .empty := by
        intro same
        have empty := (EqualityLeafProjectionPhysical.reference_empty value).mp same
        subst value
        exact empty_rejects term head
      simp [ih, nonempty]

/-- A row discarded by the source empty-child test has no finite run. -/
theorem accepted_live (edge : EdgeValue Symbol Unit) (term : Term Symbol) (accepted : EdgeAccepts edge term) :
    EqualityLeafProjectionPhysical.dead edge = false := by
  obtain ⟨terms, _, runs⟩ := accepted
  exact runs_live edge.children terms runs

/-- Actual node readback has exactly the language of the supplied physical rows. -/
theorem makeNode_exact [DecidableEq Symbol] (edges : List (EdgeValue Symbol Unit))
    (state : State Symbol Unit) (facts : Facts state) (resident : Edges state edges) (term : Term Symbol) :
    Accepts (run (makeNode edges) state).1 term ↔ ∃ edge ∈ edges, EdgeAccepts edge term := by
  rw [accepts_iff, EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident]
  constructor
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, ((EqualityLeafProjectionPhysical.normalized_member state facts.coherent edges resident edge).mp member).1,
      accepted⟩
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, (EqualityLeafProjectionPhysical.normalized_member state facts.coherent edges resident edge).mpr
      ⟨member, accepted_live edge term accepted⟩, accepted⟩

/-- Positionwise child equivalence transfers both directions of every ordered run. -/
theorem runs_equiv (relation : A → Value Symbol Unit → Prop) (meaning : A → Term Symbol → Prop)
    (requests : List A) (values : List (Value Symbol Unit))
    (related : All₂ relation requests values)
    (exact : ∀ request value, relation request value → ∀ term, Accepts value term ↔ meaning request term)
    (terms : List (Term Symbol)) : All₂ Accepts values terms ↔ All₂ meaning requests terms := by
  induction related generalizing terms with
  | nil => cases terms <;> constructor <;> intro h <;> cases h <;> exact .nil
  | @cons request value requests values head tail ih =>
      cases terms with
      | nil => constructor <;> intro h <;> cases h
      | cons term terms =>
          constructor
          · intro runs
            cases runs with
            | cons first rest => exact .cons ((exact _ _ head term).mp first) ((ih terms).mp rest)
          · intro runs
            cases runs with
            | cons first rest => exact .cons ((exact _ _ head term).mpr first) ((ih terms).mpr rest)

/-- A child result denotes precisely the common finite terms of its two operands. -/
def ChildExact (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit) : Prop :=
  ∀ term, Accepts value term ↔ Accepts pair.1 term ∧ Accepts pair.2 term

/-- The completed physical edge denotes exactly its two matching source rows. -/
theorem edge_exact (pair : EdgeValue Symbol Unit × EdgeValue Symbol Unit) (result : EdgeValue Symbol Unit)
    (symbols : pair.1.entry.key.symbol = pair.2.entry.key.symbol)
    (label : result.entry.key.symbol = pair.1.entry.key.symbol)
    (children : if pair.1.children.length = pair.2.children.length then
      All₂ ChildExact (pair.1.children.zip pair.2.children) result.children
      else result.children = [.empty]) (term : Term Symbol) :
    EdgeAccepts result term ↔ EdgeAccepts pair.1 term ∧ EdgeAccepts pair.2 term := by
  by_cases arity : pair.1.children.length = pair.2.children.length
  · simp only [arity, ↓reduceIte] at children
    have runs := fun terms => (runs_equiv ChildExact
      (fun pair term => Accepts pair.1 term ∧ Accepts pair.2 term) _ _ children
      (fun _ _ exact => exact) terms).trans
      (Language.all₂_zip_iff Accepts Accepts pair.1.children pair.2.children terms arity)
    constructor
    · rintro ⟨terms, same, accepted⟩
      have both := (runs terms).mp accepted
      exact ⟨⟨terms, by rw [← label]; exact same, both.1⟩,
        ⟨terms, by rw [← symbols, ← label]; exact same, both.2⟩⟩
    · rintro ⟨⟨terms, same, first⟩, ⟨other, secondSame, second⟩⟩
      have equal : other = terms := by
        rw [same, ← symbols] at secondSame
        exact (Term.node.inj secondSame).2.symm
      subst other
      exact ⟨terms, by rw [label]; exact same, (runs terms).mpr ⟨first, second⟩⟩
  · simp only [arity, ↓reduceIte] at children
    constructor
    · intro accepted
      have live := accepted_live result term accepted
      simp [EqualityLeafProjectionPhysical.dead, children, Value.referenceOf] at live
    · rintro ⟨⟨terms, same, first⟩, ⟨other, secondSame, second⟩⟩
      have equal : other = terms := by
        rw [same, ← symbols] at secondSame
        exact (Term.node.inj secondSame).2.symm
      subst other
      exact False.elim (arity (first.length_eq.trans second.length_eq.symm))

/-- A positionwise output relation gives exactly the same existential list membership. -/
theorem all₂_exists_iff (R : A → B → Prop) (P : A → Prop) (Q : B → Prop)
    (left : List A) (right : List B) (related : All₂ R left right)
    (exact : ∀ a b, R a b → (Q b ↔ P a)) :
    (∃ b ∈ right, Q b) ↔ ∃ a ∈ left, P a := by
  induction related with
  | nil => simp
  | @cons a b as bs head tail ih =>
      simpa only [List.mem_cons, exists_eq_or_imp] using (or_congr (exact a b head) ih)

/-- Two rows that accept the same term have the same literal root symbol. -/
theorem accepted_symbols (first second : EdgeValue Symbol Unit) (term : Term Symbol)
    (left : EdgeAccepts first term) (right : EdgeAccepts second term) :
    first.entry.key.symbol = second.entry.key.symbol := by
  obtain ⟨_, left, _⟩ := left
  obtain ⟨_, right, _⟩ := right
  rw [left] at right
  exact (Term.node.inj right).1

/-- The complete ordinary branch derives its language from the individual child calls. -/
theorem node_checked [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit))
    (checked : ∀ pair ∈ pairs left right, ∀ request ∈ pair.1.children.zip pair.2.children,
      ∀ state, Facts state → Inputs state request →
        Facts (run (call request) state).2 ∧ Available (run (call request) state).2 (run (call request) state).1 ∧
          ChildExact request (run (call request) state).1)
    (state : State Symbol Unit) (facts : Facts state) (leftResident : Edges state left) (rightResident : Edges state right) :
    let result := run (node call left right) state
    Facts result.2 ∧ Available result.2 result.1 ∧
      ∀ term, Accepts result.1 term ↔
        (∃ edge ∈ left, EdgeAccepts edge term) ∧ ∃ edge ∈ right, EdgeAccepts edge term := by
  let relation := fun (pair : EdgeValue Symbol Unit × EdgeValue Symbol Unit) (result : EdgeValue Symbol Unit) =>
    ∀ term, EdgeAccepts result term ↔ EdgeAccepts pair.1 term ∧ EdgeAccepts pair.2 term
  have edgesChecked : ∀ pair ∈ pairs left right, ∀ state, Facts state → EdgeInputs state pair →
      Facts (run (edge call pair) state).2 ∧ EdgeResident (run (edge call pair) state).2 (run (edge call pair) state).1 ∧
        relation pair (run (edge call pair) state).1 := by
    intro pair member state facts inputs
    have result := edge_checked call pair ChildExact (checked pair member) state facts inputs
    exact ⟨result.1, result.2.1, fun term => edge_exact pair _
      ((pairs_member left right pair).mp member).2.2 result.2.2.1 result.2.2.2.2 term⟩
  have inputs : ∀ pair ∈ pairs left right, EdgeInputs state pair := by
    intro pair member
    have original := (pairs_member left right pair).mp member
    exact ⟨leftResident pair.1 original.1, rightResident pair.2 original.2.1⟩
  have built := map_checked (edge call) (pairs left right) EdgeInputs EdgeResident relation
    edgeInputs_stable resident_stable edgesChecked state facts inputs
  have result := node_verified _ _ built.1 built.2.1
  simp only [node, run_bind]
  refine ⟨result.facts, result.result _ _ rfl, ?_⟩
  intro term
  rw [makeNode_exact _ _ built.1 built.2.1 term]
  rw [all₂_exists_iff relation (fun pair => EdgeAccepts pair.1 term ∧ EdgeAccepts pair.2 term)
    (fun result => EdgeAccepts result term) _ _ built.2.2 (fun _ _ correct => correct term)]
  constructor
  · rintro ⟨pair, member, first, second⟩
    have original := (pairs_member left right pair).mp member
    exact ⟨⟨pair.1, original.1, first⟩, ⟨pair.2, original.2.1, second⟩⟩
  · rintro ⟨⟨first, firstIn, firstAccepted⟩, ⟨second, secondIn, secondAccepted⟩⟩
    exact ⟨(first, second), (pairs_member left right _).mpr
      ⟨firstIn, secondIn, accepted_symbols first second term firstAccepted secondAccepted⟩, firstAccepted, secondAccepted⟩

end MicroCFTA.SourceInternedIntersectionRows
