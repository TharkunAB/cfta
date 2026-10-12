import MicroCFTA.SupportTerms
import MicroCFTA.BinderLanguage

/-!
# Generator support constructors

These constructors copy the ordinary edges made by `Gen.Internal.Support`.
Operands use the full least-language semantics. They can contain recursion.
The new wrapper edges have exactly the source paths and child order.
-/
namespace MicroCFTA.SupportGraph
open Language GeneratorCombinators Binding BinderLanguage

/-- A support graph shape keeps every edge predicate. -/
abbrev Support (Symbol : Type) := Shape (Payload (Label Symbol))

/-- One unconstrained support edge. Interning does not change its language. -/
def edge (label : Label Symbol) (children : List (Support Symbol)) : Support Symbol :=
  .branch ⟨label, fun _ => True⟩ children

/-- The exact finite term graph built by `singletonNode`. -/
def singleton : Term (Label Symbol) → Support Symbol
  | .node label children => edge label (children.map singleton)

/-- An ordered forest denotes exactly pointwise acceptance in its child supports. -/
theorem forest_all₂ (environment : Env (Label Symbol)) (supports : List (Support Symbol))
    (terms : List (Term (Label Symbol))) :
    forest environment supports terms ↔ All₂ (meaning environment) supports terms := by
  induction supports generalizing terms with
  | nil =>
    cases terms with
    | nil => simp only [forest]; exact ⟨fun _ => .nil, fun _ => trivial⟩
    | cons first rest => simp only [forest]; exact ⟨fun h => False.elim h, fun h => by cases h⟩
  | cons first rest ih =>
    cases terms with
    | nil => simp only [forest]; exact ⟨fun h => False.elim h, fun h => by cases h⟩
    | cons term terms =>
      simp only [forest]
      constructor
      · intro accepted
        exact .cons accepted.1 ((ih terms).mp accepted.2)
      · intro accepted
        cases accepted with
        | cons head tail => exact ⟨head, (ih terms).mpr tail⟩

/-- A singleton graph accepts only its source term, even in an open binder environment. -/
theorem singleton_exact (environment : Env (Label Symbol)) (source term : Term (Label Symbol)) :
    meaning environment (singleton source) term ↔ term = source := by
  induction source using Term.rec
    (motive_2 := fun sources => ∀ terms, forest environment (sources.map singleton) terms ↔ terms = sources)
    generalizing term with
  | node label children ih =>
    simp only [singleton, edge, meaning]
    simp [ih]
  | nil => rename_i terms; cases terms <;> simp [forest]
  | cons first rest ih ir =>
    rename_i terms
    cases terms with
    | nil => simp [forest]
    | cons term terms => simp [forest, ih, ir]

/-- A family uses one keyed edge for each supplied body. -/
def family (keyed : List (Nat × Support Symbol)) : Support Symbol :=
  .alternatives (keyed.map fun (key, body) =>
    edge .family [singleton (.node (.key key) []), body])

/-- A family term retains its key and its complete body term. -/
def familyTerm (key : Nat) (body : Term (Label Symbol)) : Term (Label Symbol) :=
  .node .family [.node (.key key) [], body]

/-- Family construction neither loses nor adds a member of any keyed body. -/
theorem family_exact (environment : Env (Label Symbol)) (keyed : List (Nat × Support Symbol))
    (term : Term (Label Symbol)) :
    meaning environment (family keyed) term ↔
      ∃ key body, (key, body) ∈ keyed ∧ ∃ child,
        meaning environment body child ∧ term = familyTerm key child := by
  simp only [family, meaning]
  constructor
  · rintro ⟨⟨shape, member⟩, accepted⟩
    obtain ⟨⟨key, body⟩, inputMember, rfl⟩ := List.mem_map.mp member
    simp only [edge, meaning] at accepted
    obtain ⟨children, rfl, accepted, _⟩ := accepted
    cases children with
    | nil => simp [forest] at accepted
    | cons first rest => cases rest with
      | nil => simp [forest] at accepted
      | cons child rest =>
        simp only [forest] at accepted
        have firstEq := (singleton_exact environment _ first).mp accepted.1
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest
        exact ⟨key, body, inputMember, child, accepted.2.1, by simp [familyTerm, firstEq]⟩
  · rintro ⟨key, body, member, child, accepted, rfl⟩
    refine ⟨⟨_, List.mem_map.mpr ⟨(key, body), member, rfl⟩⟩, ?_⟩
    simp only [edge, meaning]
    refine ⟨_, rfl, ?_, trivial⟩
    simp only [forest]
    exact ⟨(singleton_exact environment _ _).mpr rfl, accepted, trivial⟩

/-- The source ties its selected key to the first child of the family term. -/
def restrictKey (key : Nat) (body : Support Symbol) : Support Symbol :=
  .branch ⟨.atKey, fun term => PathsEqual term [0] [1, 0]⟩
    [singleton (.node (.key key) []), body]

/-- A successful restriction keeps exactly terms whose family key exists and agrees. -/
theorem restrict_exact (environment : Env (Label Symbol)) (key : Nat)
    (body : Support Symbol) (term : Term (Label Symbol)) :
    meaning environment (restrictKey key body) term ↔
      ∃ child, meaning environment body child ∧
        child.atPath [0] = some (.node (.key key) []) ∧
        term = .node .atKey [.node (.key key) [], child] := by
  simp only [restrictKey, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, same⟩
    cases children with
    | nil => simp [forest] at accepted
    | cons first rest => cases rest with
      | nil => simp [forest] at accepted
      | cons child rest =>
        simp only [forest] at accepted
        have firstEq := (singleton_exact environment _ first).mp accepted.1
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest; subst first
        refine ⟨child, accepted.2.1, ?_, rfl⟩
        simpa [PathsEqual, Term.atPath] using same
  · rintro ⟨child, accepted, found, rfl⟩
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [forest]
      exact ⟨(singleton_exact environment _ _).mpr rfl, accepted, trivial⟩
    · simpa [PathsEqual, Term.atPath] using found

/-- Restricting a complete family accepts exactly the bodies stored under the selected key. -/
theorem restrict_family_exact (environment : Env (Label Symbol))
    (keyed : List (Nat × Support Symbol)) (key : Nat) (term : Term (Label Symbol)) :
    meaning environment (restrictKey key (family keyed)) term ↔
      ∃ body, (key, body) ∈ keyed ∧ ∃ child, meaning environment body child ∧
        term = .node .atKey [.node (.key key) [], familyTerm key child] := by
  rw [restrict_exact]
  constructor
  · rintro ⟨child, accepted, found, rfl⟩
    obtain ⟨other, body, member, value, bodyAccepted, rfl⟩ := (family_exact environment keyed child).mp accepted
    have same : other = key := by simpa [familyTerm, Term.atPath] using found
    subst other
    exact ⟨body, member, value, bodyAccepted, rfl⟩
  · rintro ⟨body, member, child, accepted, rfl⟩
    exact ⟨_, (family_exact environment keyed _).mpr ⟨key, body, member, child, accepted, rfl⟩,
      by simp [familyTerm, Term.atPath], rfl⟩

end MicroCFTA.SupportGraph
