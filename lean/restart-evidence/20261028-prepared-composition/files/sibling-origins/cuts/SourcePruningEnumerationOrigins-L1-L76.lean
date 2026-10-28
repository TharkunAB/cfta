import MicroCFTA.EnumerationSchedule

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
