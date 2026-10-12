import MicroCFTA.SupportGraph

/-!
# N-way support joins

The centre stores the operation before its keys. Each argument stores its
key before its support. Equality paths connect those two existing keys.
-/
namespace MicroCFTA.SupportJoin
open Language GeneratorCombinators BinderLanguage SupportGraph

/-- The key terms in source argument order. -/
def keys (component first : Nat) : Nat → List (Term (Label Symbol))
  | 0 => []
  | count + 1 => .node (.argKey component first) [] :: keys component (first + 1) count

/-- Wrap argument terms with their positional keys. -/
def arguments (component first : Nat) : List (Term (Label Symbol)) → List (Term (Label Symbol))
  | [] => []
  | term :: rest => .node .argKeyed [.node (.argKey component first) [], term] :: arguments component (first + 1) rest

/-- The source argument support edges. -/
def argumentNodes (component first : Nat) : List (Support Symbol) → List (Support Symbol)
  | [] => []
  | body :: rest => edge .argKeyed [singleton (.node (.argKey component first) []), body] :: argumentNodes component (first + 1) rest

/-- A key is present at every valid argument position. -/
theorem keys_lookup (component first count index : Nat) (inside : index < count) :
    (keys (Symbol := Symbol) component first count)[index]? = some (.node (.argKey component (first + index)) []) := by
  induction count generalizing first index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp [keys]
    | succ index =>
      simpa [keys, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1) index (by omega)

/-- Every argument wrapper uses the key for its exact list position. -/
theorem arguments_lookup (component first : Nat) (terms : List (Term (Label Symbol)))
    (index : Nat) (inside : index < terms.length) :
    (arguments component first terms)[index]? =
      some (.node .argKeyed [.node (.argKey component (first + index)) [], terms[index]]) := by
  induction terms generalizing first index with
  | nil => simp at inside
  | cons term rest ih =>
    cases index with
    | zero => simp [arguments]
    | succ index =>
      simpa [arguments, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1) index (by simpa using inside)

/-- The source callback retains the complete operation and every argument. -/
def joinTerm (component : Nat) (operation : Term (Label Symbol)) (terms : List (Term (Label Symbol))) : Term (Label Symbol) :=
  .node .joinN (.node .centerKeyed (operation :: keys component 0 terms.length) :: arguments component 0 terms)

/-- Every equality emitted by the join constructor holds on its callback term. -/
theorem join_equalities (component : Nat) (operation : Term (Label Symbol)) (terms : List (Term (Label Symbol)))
    (index : Nat) (inside : index < terms.length) :
    PathsEqual (joinTerm component operation terms) [0, index + 1] [index + 1, 0] := by
  have left := keys_lookup (Symbol := Symbol) component 0 terms.length index inside
  have right := arguments_lookup component 0 terms index inside
  simp only [Nat.zero_add] at left right
  simp [PathsEqual, joinTerm, Term.atPath, left, right]

/-- A list of singleton support graphs accepts precisely its input forest. -/
theorem singletons_exact (environment : Env (Label Symbol)) (source terms : List (Term (Label Symbol))) :
    forest environment (source.map singleton) terms ↔ terms = source := by
  induction source generalizing terms with
  | nil => cases terms <;> simp [forest]
  | cons first rest ih => cases terms with
    | nil => simp [forest]
    | cons term terms => simp [forest, singleton_exact, ih]

/-- Argument wrapping retains each operand language and its original position. -/
theorem arguments_exact (environment : Env (Label Symbol)) (component first : Nat)
    (supports : List (Support Symbol)) (terms : List (Term (Label Symbol))) :
    forest environment (argumentNodes component first supports) terms ↔
      ∃ values, forest environment supports values ∧ terms = arguments component first values := by
  induction supports generalizing first terms with
  | nil =>
    constructor
    · intro accepted
      have empty : terms = [] := by cases terms <;> simp_all [argumentNodes, forest]
      subst terms
      exact ⟨[], by simp [forest], rfl⟩
    · rintro ⟨values, accepted, rfl⟩
      have empty : values = [] := by cases values <;> simp_all [forest]
      subst values
      simp [arguments, argumentNodes, forest]
  | cons body rest ih =>
    cases terms with
    | nil =>
      constructor
      · simp [argumentNodes, forest]
      · rintro ⟨values, accepted, same⟩
        cases values with
        | nil => simp [forest] at accepted
        | cons value values => simp [arguments] at same
    | cons term terms =>
      simp only [argumentNodes, forest]
      constructor
      · rintro ⟨head, tail⟩
        simp only [edge, meaning] at head
        obtain ⟨children, rfl, head, _⟩ := head
        cases children with
        | nil => simp [forest] at head
        | cons key children => cases children with
          | nil => simp [forest] at head
          | cons value children =>
            simp only [forest] at head
            have keyEq := (singleton_exact environment _ key).mp head.1
            have empty : children = [] := by cases children <;> simp_all [forest]
            subst children
            obtain ⟨values, accepted, rfl⟩ := (ih (first + 1) terms).mp tail
            refine ⟨value :: values, ?_, ?_⟩
            · simp only [forest]; exact ⟨head.2.1, accepted⟩
            · simp [arguments, keyEq]
      · rintro ⟨values, accepted, same⟩
        cases values with
        | nil => simp [forest] at accepted
        | cons value values =>
          simp only [forest] at accepted
          simp only [arguments, List.cons.injEq] at same
          rcases same with ⟨rfl, rfl⟩
          refine ⟨?_, (ih (first + 1) _).mpr ⟨values, accepted.2, rfl⟩⟩
          simp only [edge, meaning]
          refine ⟨_, rfl, ?_, trivial⟩
          simp only [forest]
          exact ⟨(singleton_exact environment _ _).mpr rfl, accepted.1, trivial⟩

/-- The source joins one centre and all argument supports with its equality classes. -/
def joinNode (component : Nat) (operation : Support Symbol) (supports : List (Support Symbol)) : Support Symbol :=
  .branch ⟨.joinN, fun term => ∀ index < supports.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩
    (edge .centerKeyed (operation :: (keys component 0 supports.length).map singleton) :: argumentNodes component 0 supports)

/-- The centre contains exactly one operation term followed by the specified key forest. -/
theorem center_exact (environment : Env (Label Symbol)) (operation : Support Symbol)
    (keyTerms : List (Term (Label Symbol))) (term : Term (Label Symbol)) :
    meaning environment (edge .centerKeyed (operation :: keyTerms.map singleton)) term ↔
      ∃ value, meaning environment operation value ∧ term = .node .centerKeyed (value :: keyTerms) := by
  simp only [edge, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    cases children with
    | nil => simp [forest] at accepted
    | cons value values =>
      simp only [forest] at accepted
      exact ⟨value, accepted.1, by rw [(singletons_exact environment keyTerms values).mp accepted.2]⟩
  · rintro ⟨value, accepted, rfl⟩
    refine ⟨_, rfl, ?_, trivial⟩
    simp only [forest]
    exact ⟨accepted, (singletons_exact environment keyTerms keyTerms).mpr rfl⟩

/-- The complete joined graph accepts exactly the source callback's operand product. -/
theorem join_exact (environment : Env (Label Symbol)) (component : Nat) (operation : Support Symbol)
    (supports : List (Support Symbol)) (term : Term (Label Symbol)) :
    meaning environment (joinNode component operation supports) term ↔
      ∃ operationTerm terms, meaning environment operation operationTerm ∧
        forest environment supports terms ∧ term = joinTerm component operationTerm terms := by
  simp only [joinNode, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    cases children with
    | nil => simp [forest] at accepted
    | cons center rest =>
      simp only [forest] at accepted
      obtain ⟨operationTerm, operationAccepted, rfl⟩ := (center_exact environment operation _ center).mp accepted.1
      obtain ⟨terms, termsAccepted, rfl⟩ := (arguments_exact environment component 0 supports rest).mp accepted.2
      have size := ((forest_all₂ environment supports terms).mp termsAccepted).length_eq
      exact ⟨operationTerm, terms, operationAccepted, termsAccepted, by simp [joinTerm, size]⟩
  · rintro ⟨operationTerm, terms, operationAccepted, termsAccepted, rfl⟩
    have size := ((forest_all₂ environment supports terms).mp termsAccepted).length_eq
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [forest]
      constructor
      · apply (center_exact environment operation _ _).mpr
        exact ⟨operationTerm, operationAccepted, by simp [size]⟩
      · exact (arguments_exact environment component 0 supports _).mpr ⟨terms, termsAccepted, rfl⟩
    · intro index inside
      exact join_equalities component operationTerm terms index (size ▸ inside)

end MicroCFTA.SupportJoin
