import MicroCFTA.EnumerationCorrectness

/-!
# Original term paths for allocated enumeration variables

An origin is an actual path in the original complete term.
Assignment extension retains these paths for every allocated variable.
Empty equality classes use the current term as their fresh witness.
-/
namespace MicroCFTA.SourcePruningEnumerationOrigins
open Language EnumerationState EnumerationCorrectness
variable {Symbol Guard : Type}

/-- A term is the subtree at one path in the original complete term. -/
def Origin (whole term : Term Symbol) : Prop :=
  ∃ path : List Nat, whole.atPath path = some term

/-- Every allocated variable denotes a subtree of the original term. -/
def AssignmentOrigins (whole : Term Symbol) (limit : Nat)
    (assignment : Nat → Term Symbol) : Prop :=
  ∀ uv < limit, Origin whole (assignment uv)

/-- The empty path denotes the original term. -/
theorem origin_refl (whole : Term Symbol) : Origin whole whole := ⟨[], rfl⟩

/-- Concatenation retains the original path of a nested subtree. -/
theorem origin_trans (whole middle term : Term Symbol)
    (parent : Origin whole middle) (nested : Origin middle term) : Origin whole term := by
  obtain ⟨first, atFirst⟩ := parent
  obtain ⟨rest, atRest⟩ := nested
  refine ⟨first ++ rest, ?_⟩
  rw [atPath_append, atFirst]
  exact atRest

/-- An existing path below an original subtree retains its origin. -/
theorem origin_atPath (whole middle term : Term Symbol) (path : List Nat)
    (parent : Origin whole middle) (found : middle.atPath path = some term) : Origin whole term :=
  origin_trans whole middle term parent ⟨path, found⟩

/-- Each child of an original subtree has an original path. -/
theorem origin_child (whole : Term Symbol) (symbol : Symbol) (children : List (Term Symbol))
    (child : Term Symbol) (parent : Origin whole (.node symbol children)) (member : child ∈ children) :
    Origin whole child := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  apply origin_atPath whole (.node symbol children) child [index] parent
  simp only [Term.atPath, found, Option.bind_some]

/-- An original subtree has no greater height than the original term. -/
theorem origin_height (whole term : Term Symbol) (origin : Origin whole term) :
    term.height ≤ whole.height := by
  obtain ⟨path, found⟩ := origin
  have bounded := atPath_height_bound whole term path found
  omega

/-- A smaller allocation prefix retains every original path. -/
theorem assignment_origins_mono (whole : Term Symbol) (low high : Nat)
    (assignment : Nat → Term Symbol) (bounded : low ≤ high)
    (origins : AssignmentOrigins whole high assignment) : AssignmentOrigins whole low assignment := by
  intro uv inside
  exact origins uv (Nat.lt_of_lt_of_le inside bounded)

/-- Agreement on allocated variables retains their original paths. -/
theorem assignment_origins_congr (whole : Term Symbol) (limit : Nat)
    (assignment extended : Nat → Term Symbol)
    (origins : AssignmentOrigins whole limit assignment)
    (agree : ∀ uv < limit, extended uv = assignment uv) : AssignmentOrigins whole limit extended := by
  intro uv inside
  rw [agree uv inside]
  exact origins uv inside

/-- Installing original subtrees retains origins at every old and fresh variable. -/
theorem install_origins (assignment : Nat → Term Symbol) (start : Nat)
    (terms : List (Term Symbol)) (whole : Term Symbol)
    (old : AssignmentOrigins whole start assignment)
    (fresh : ∀ term ∈ terms, Origin whole term) :
    AssignmentOrigins whole (start + terms.length) (install assignment start terms) := by
  induction terms generalizing assignment start with
  | nil => simpa only [List.length_nil, Nat.add_zero, install] using old
  | cons term rest ih =>
      change AssignmentOrigins whole (start + (rest.length + 1))
        (install (fun uv => if uv = start then term else assignment uv) (start + 1) rest)
      have initial : AssignmentOrigins whole (start + 1)
          (fun uv => if uv = start then term else assignment uv) := by
        intro uv inside
        by_cases same : uv = start
        · simp only [same, ↓reduceIte]
          exact fresh term (by simp)
        · simp only [same, ↓reduceIte]
          exact old uv (by omega)
      have result := ih (start := start + 1) _ initial (fun child member => fresh child (by simp [member]))
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- Satisfied equality classes admit witnesses with paths in the original term. -/
theorem equality_witnesses_origins (whole term : Term Symbol) (tries : List EqualityTrie.Trie)
    (origin : Origin whole term) (holds : ∀ trie ∈ tries, EqualityHolds term trie) :
    ∃ witnesses, All₂ (fun trie common => ∀ path ∈ EqualityTrie.fromPathTrie trie,
      term.atPath path = some common) tries witnesses ∧
      ∀ witness ∈ witnesses, Origin whole witness := by
  induction tries with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons trie rest ih =>
      obtain ⟨witnesses, related, origins⟩ := ih (fun next member => holds next (by simp [member]))
      by_cases empty : EqualityTrie.fromPathTrie trie = []
      · refine ⟨term :: witnesses, .cons ?_ related, ?_⟩
        · simp only [empty, List.not_mem_nil, false_implies, implies_true]
        · intro witness member
          rcases List.mem_cons.mp member with rfl | member
          · exact origin
          · exact origins witness member
      · obtain ⟨common, paths⟩ := holds trie (by simp)
        obtain ⟨path, member⟩ := List.exists_mem_of_ne_nil _ empty
        refine ⟨common :: witnesses, .cons paths related, ?_⟩
        intro witness present
        rcases List.mem_cons.mp present with rfl | present
        · exact origin_atPath whole term _ path origin (paths path member)
        · exact origins witness present

/-- Fresh equality allocation retains one model and all original variable paths. -/
theorem suspended_counter (count : Nat) (state : State Symbol Guard) :
    (suspendedState count state).counter = state.counter + count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [suspendedState, ih]
      change state.counter + 1 + count = state.counter + (count + 1)
      omega

/-- Fresh equality allocation retains one model and all original variable paths. -/
theorem fresh_classes_state_complete_origins
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (valid : StorageValid state) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment state) (whole term : Term Symbol)
    (tries : List EqualityTrie.Trie) (equalities : ∀ trie ∈ tries, EqualityHolds term trie)
    (old : AssignmentOrigins whole state.counter assignment) (origin : Origin whole term) :
    ∃ extended, Satisfies language meaning extended (suspendedState tries.length state) ∧
      (∀ uv < state.counter, extended uv = assignment uv) ∧
      (∀ sc ∈ suspendedVars state.counter tries, Suspended.Holds extended term sc) ∧
      AssignmentOrigins whole (suspendedState tries.length state).counter extended := by
  obtain ⟨witnesses, related, origins⟩ := equality_witnesses_origins whole term tries origin equalities
  let extended := install assignment state.counter witnesses
  have agree : ∀ uv < state.counter, extended uv = assignment uv := install_before assignment _ witnesses
  have original := (state_assignment_congr language meaning state valid extended assignment agree).mpr satisfied
  refine ⟨extended, (suspendMany_semantics language meaning extended tries.length state valid.aligned).mpr original,
    agree, installed_classes term tries witnesses related assignment state.counter, ?_⟩
  have sameLength := related.length_eq
  have fresh := install_origins assignment state.counter witnesses whole old origins
  rw [suspended_counter, sameLength]
  exact fresh

end MicroCFTA.SourcePruningEnumerationOrigins
