import MicroCFTA.SourceEqualityNeeded
import MicroCFTA.SymbolicSignedPaths

/-!
# Independent term meaning of the source required-path trie

Each stored child key requires an existing child and the requirements below
that key. This meaning does not use the source graph transformation. It
permits duplicate input paths and paths that extend other input paths.
-/
namespace MicroCFTA.SourceEqualityNeededMeaning
open Language SourceEqualityNeeded SourceEqualityNeededMap

/-- Read one signed child position with the source negative-index behavior. -/
def childAt (children : List (Term Symbol)) (index : Int) : Option (Term Symbol) :=
  if index < 0 then none else children[index.toNat]?

/-- One signed path step is a child lookup followed by its suffix lookup. -/
theorem lookup_cons (symbol : Symbol) (children : List (Term Symbol)) (index : Int) (rest : Path) :
    SymbolicSignedPaths.lookup (.node symbol children) (index :: rest) =
      (childAt children index).bind (fun child => SymbolicSignedPaths.lookup child rest) := by
  rw [SymbolicSignedPaths.lookup]
  unfold childAt
  split <;> rfl

/-- Signed path concatenation retains the intermediate subtree. -/
theorem lookup_append (term : Term Symbol) (initial rest : Path) :
    SymbolicSignedPaths.lookup term (initial ++ rest) =
      (SymbolicSignedPaths.lookup term initial).bind (fun child => SymbolicSignedPaths.lookup child rest) := by
  induction initial generalizing term with
  | nil => rfl
  | cons index initial ih =>
      cases term with
      | node symbol children =>
          rw [List.cons_append, lookup_cons, lookup_cons]
          cases selected : childAt children index with
          | none => rfl
          | some child => simpa only [Option.bind_some] using ih child

/-- An existing subtree at a path implies an existing subtree at every prefix. -/
theorem prefix_exists (term : Term Symbol) (initial path : Path) (prefixOf : initial.IsPrefix path)
    (existsPart : ∃ part, SymbolicSignedPaths.lookup term path = some part) :
    ∃ part, SymbolicSignedPaths.lookup term initial = some part := by
  obtain ⟨rest, rfl⟩ := prefixOf
  obtain ⟨part, found⟩ := existsPart
  rw [lookup_append] at found
  obtain ⟨middle, selected, _⟩ := Option.bind_eq_some_iff.mp found
  exact ⟨middle, selected⟩

/-- Every stored child requirement is checked on an existing ordered child. -/
def Matches : Needed → Term Symbol → Prop
  | .node children, .node _ terms =>
      ∀ index needed, (index, needed) ∈ children →
        ∃ term, childAt terms index = some term ∧ Matches needed term
termination_by needed _ => sizeOf needed
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, needed) ∈ children›
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Empty requirements accept every finite term. -/
theorem matches_empty (term : Term Symbol) : Matches empty term := by
  cases term
  simp [Matches, empty]

/-- Trie matching supplies an actual subtree at every demanded path. -/
theorem matches_lookup (needed : Needed) (valid : Valid needed) (term : Term Symbol)
    (matched : Matches needed term) (path : Path) (required : demands needed path = true) :
    ∃ part, SymbolicSignedPaths.lookup term path = some part := by
  induction path generalizing needed term with
  | nil => exact ⟨term, rfl⟩
  | cons index rest ih =>
      cases needed with
      | node children =>
          cases term with
          | node symbol terms =>
              rw [Valid] at valid
              rw [Matches] at matched
              simp only [demands] at required
              cases found : SourceEqualityNeededMap.lookup index children with
              | none => simp [found] at required
              | some child =>
                  have member := lookup_mem index children child found
                  obtain ⟨subtree, selected, matchesChild⟩ := matched index child member
                  obtain ⟨part, reached⟩ := ih child (valid.2 index child member) subtree matchesChild
                    (by simpa only [found] using required)
                  exact ⟨part, by rw [lookup_cons, selected, Option.bind_some, reached]⟩

/-- Actual subtrees at every demanded path supply the structural trie match. -/
theorem matches_of_lookup (needed : Needed) (valid : Valid needed) (term : Term Symbol)
    (allPaths : ∀ path, demands needed path = true → ∃ part, SymbolicSignedPaths.lookup term path = some part) :
    Matches needed term := by
  cases shape : needed with
  | node children =>
      cases term with
      | node symbol terms =>
          rw [shape] at valid allPaths
          rw [Valid] at valid
          rw [Matches]
          intro index child member
          have found := lookup_of_mem index children child valid.1 member
          have oneStep : demands (.node children) [index] = true := by simp [demands, found]
          obtain ⟨subtree, selected⟩ := allPaths [index] oneStep
          have childSelected : childAt terms index = some subtree := by
            rw [lookup_cons] at selected
            cases foundChild : childAt terms index with
            | none =>
                simp only [foundChild, Option.bind_none] at selected
                cases selected
            | some value =>
                have same : value = subtree := by
                  simpa only [foundChild, Option.bind_some, SymbolicSignedPaths.lookup, Option.some.injEq] using selected
                exact congrArg some same
          refine ⟨subtree, childSelected, matches_of_lookup child (valid.2 index child member) subtree ?_⟩
          intro suffix required
          have whole : demands (.node children) (index :: suffix) = true := by simp [demands, found, required]
          obtain ⟨part, reached⟩ := allPaths (index :: suffix) whole
          exact ⟨part, by simpa only [lookup_cons, childSelected, Option.bind_some] using reached⟩
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Structural matching is exactly existence of every represented path. -/
theorem matches_exact (needed : Needed) (valid : Valid needed) (term : Term Symbol) :
    Matches needed term ↔
      ∀ path, demands needed path = true → ∃ part, SymbolicSignedPaths.lookup term path = some part :=
  ⟨fun matched path required => matches_lookup needed valid term matched path required,
    matches_of_lookup needed valid term⟩

/-- The actual source right fold denotes exactly its complete required-path set. -/
theorem build_exact (paths : List Path) (term : Term Symbol) :
    Matches (build paths) term ↔
      ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup term path = some part := by
  rw [matches_exact (build paths) (build_valid paths)]
  constructor
  · intro allPaths path member
    exact allPaths path ((demands_build paths path).mpr (Or.inr ⟨path, member, ⟨[], by simp⟩⟩))
  · intro allPaths path required
    rcases (demands_build paths path).mp required with root | ⟨original, member, initial⟩
    · subst path; exact ⟨term, rfl⟩
    · exact prefix_exists term path original initial (allPaths original member)

/-- Each source insertion conjoins its complete path requirement. -/
theorem insert_exact (path : Path) (needed : Needed) (valid : Valid needed) (term : Term Symbol) :
    Matches (insert path needed) term ↔
      Matches needed term ∧ ∃ part, SymbolicSignedPaths.lookup term path = some part := by
  rw [matches_exact (insert path needed) (insert_valid path needed valid)]
  constructor
  · intro allPaths
    refine ⟨(matches_exact needed valid term).mpr ?_, ?_⟩
    · intro query required
      exact allPaths query ((demands_insert path needed valid query).mpr (Or.inl required))
    · exact allPaths path ((demands_insert path needed valid path).mpr (Or.inr ⟨[], by simp⟩))
  · rintro ⟨matched, existing⟩ query required
    rcases (demands_insert path needed valid query).mp required with previous | initial
    · exact matches_lookup needed valid term matched query previous
    · exact prefix_exists term query path initial existing

/-- The source greatest-key row filter cannot reject a matching finite term. -/
theorem matching_row_fits (needed : Needed) (valid : Valid needed) (symbol : Symbol)
    (children : List (Term Symbol)) (matched : Matches needed (.node symbol children)) :
    fits needed children.length = true := by
  rw [fits_exact needed valid children.length]
  intro index required
  obtain ⟨part, found⟩ := matches_lookup needed valid (.node symbol children) matched [index] required
  have checked := SymbolicSignedPaths.lookup_fitsPath symbol children [index] part found
  simp only [SymbolicSignedPaths.fitsPath, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1

/-- Equal required path sets have equal term meanings, regardless of insertion order. -/
theorem build_extensional (first second : List Path)
    (same : ∀ path, path ∈ first ↔ path ∈ second) (term : Term Symbol) :
    Matches (build first) term ↔ Matches (build second) term := by
  rw [build_exact, build_exact]
  exact ⟨fun allPaths path member => allPaths path ((same path).mpr member),
    fun allPaths path member => allPaths path ((same path).mp member)⟩

/-- Empty, duplicate, and prefix path inputs all impose their stated requirements. -/
theorem prefix_duplicate_example (term : Term Symbol) :
    Matches (build [[], [0], [0, 1], [0]]) term ↔
      ∃ part, SymbolicSignedPaths.lookup term [0, 1] = some part := by
  rw [build_exact]
  constructor
  · intro allPaths; exact allPaths [0, 1] (by simp)
  · intro found path member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨term, rfl⟩
    · exact prefix_exists term [0] [0, 1] ⟨[1], rfl⟩ found
    · exact found
    · exact prefix_exists term [0] [0, 1] ⟨[1], rfl⟩ found

/-- A negative source key has no subtree, despite its maximum-key row test. -/
theorem negative_has_no_match (term : Term Symbol) : ¬ Matches (build [[-1]]) term := by
  rw [build_exact]
  intro allPaths
  obtain ⟨part, found⟩ := allPaths [-1] (by simp)
  cases term
  simp [SymbolicSignedPaths.lookup] at found

end MicroCFTA.SourceEqualityNeededMeaning
