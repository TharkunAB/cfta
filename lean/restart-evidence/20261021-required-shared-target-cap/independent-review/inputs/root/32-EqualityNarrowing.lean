import MicroCFTA.PathFilter
import MicroCFTA.SymbolicGraph
import MicroCFTA.EqualityNormalize

/-!
# No-loss laws for equality-driven path intersections

Each equality edit intersects one selected path with the projections at all
other paths in its class. The projections may contain extra terms. Coverage
of the original subterms suffices to retain every term that satisfies the
class. The original edge guard stays attached to every copied constructor.
-/

namespace MicroCFTA.EqualityNarrowing
open Language EqualityNormalize

/-- The source intersects every nonempty projected list and uses empty for an empty list. -/
def common : List (Term Symbol → Prop) → Term Symbol → Prop
  | [], _ => False
  | first :: rest, term => first term ∧ ∀ language ∈ rest, language term

/-- A nonempty intersection contains exactly the common projected terms. -/
theorem common_exact (languages : List (Term Symbol → Prop)) (nonempty : languages ≠ []) (term : Term Symbol) :
    common languages term ↔ ∀ language ∈ languages, language term := by
  cases languages with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => simp [common]

/-- All paths other than the edited path contribute one projection. -/
def others (paths : Class) (selected : Path) : List Path := paths.filter (fun path => decide (path ≠ selected))

/-- A nontrivial class always has another distinct path for every selected member. -/
theorem others_nonempty (paths : Class) (active : Nontrivial paths) (selected : Path) :
    others paths selected ≠ [] := by
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  intro empty
  have no : ∀ path ∈ paths, path = selected := by
    intro path member
    apply Classical.byContradiction
    intro different
    have present : path ∈ others paths selected := by simp [others, member, different]
    simp [empty] at present
  exact different ((no left leftMember).trans (no right rightMember).symm)

/-- The source path projection retains every accepted subtree, with its own guard. -/
def projected [DecidableEq State] (graph : Automaton State Symbol) (root : State) (path : Path) : Term Symbol → Prop :=
  SymbolicGraph.AcceptsRows graph (SymbolicGraph.projectRows graph path root)

/-- The actual other-path intersection used to narrow one class member. -/
def otherIntersection [DecidableEq State] (graph : Automaton State Symbol) (root : State)
    (paths : Class) (selected : Path) : Term Symbol → Prop :=
  common ((others paths selected).map (projected graph root))

/-- Equality supplies one existing subtree in every other-path projection. -/
theorem selected_common [DecidableEq State] (graph : Automaton State Symbol) (root : State)
    (paths : Class) (active : Nontrivial paths) (selected : Path) (member : selected ∈ paths)
    (term : Term Symbol) (accepted : Accepts graph root term) (satisfied : ClassSat term paths) :
    ∃ subtree, term.atPath selected = some subtree ∧ otherIntersection graph root paths selected subtree := by
  obtain ⟨subtree, found⟩ := class_member_exists term paths active satisfied selected member
  refine ⟨subtree, found, ?_⟩
  apply (common_exact _ (by simpa using others_nonempty paths active selected) subtree).mpr
  intro language present
  obtain ⟨path, pathMember, rfl⟩ := List.mem_map.mp present
  have original : path ∈ paths := (List.mem_filter.mp pathMember).1
  obtain ⟨value, selectedValue, pathValue⟩ := class_pair_equal term paths active satisfied selected path member original
  have same : value = subtree := Option.some.inj (selectedValue.symm.trans found)
  subst value
  exact SymbolicGraph.project_coverage graph root path term subtree accepted pathValue

/-- Boolean membership is used only to interpret the intersected graph language. -/
noncomputable def otherTest [DecidableEq State] (graph : Automaton State Symbol) (root : State)
    (paths : Class) (selected : Path) (term : Term Symbol) : Bool :=
  @decide (otherIntersection graph root paths selected term) (Classical.propDecidable _)

/-- The edited graph can never add an original rejected term. -/
theorem edit_sound [DecidableEq State] (source : Automaton State Symbol) (root : State)
    (paths : Class) (selected : Path) (current : Automaton Current Symbol) (state : Current) (term : Term Symbol)
    (accepted : Accepts (PathFilter.restrict false current)
      (state, PathFilter.pathPlan (otherTest source root paths selected) selected) term) :
    Accepts current state term := (PathFilter.restrict_sound false current accepted).1

/-- One equality edit retains a valid original term in any already narrowed graph. -/
theorem edit_preserves [DecidableEq State] (source : Automaton State Symbol) (root : State)
    (paths : Class) (active : Nontrivial paths) (selected : Path) (member : selected ∈ paths)
    (current : Automaton Current Symbol) (state : Current) (term : Term Symbol)
    (original : Accepts source root term) (retained : Accepts current state term) (satisfied : ClassSat term paths) :
    Accepts (PathFilter.restrict false current)
      (state, PathFilter.pathPlan (otherTest source root paths selected) selected) term := by
  classical
  apply (PathFilter.restrict_exact false current state _ term).mpr
  refine ⟨retained, ?_⟩
  rw [PathFilter.at_exact]
  obtain ⟨subtree, found, included⟩ := selected_common source root paths active selected member term original satisfied
  simp only [found]
  exact decide_eq_true included

/-- The selected-path intersection preserves the complete equality-constrained language. -/
theorem edit_exact [DecidableEq State] (graph : Automaton State Symbol) (root : State)
    (paths : Class) (active : Nontrivial paths) (selected : Path) (member : selected ∈ paths) (term : Term Symbol) :
    (Accepts (PathFilter.restrict false graph)
        (root, PathFilter.pathPlan (otherTest graph root paths selected) selected) term ∧ ClassSat term paths) ↔
      Accepts graph root term ∧ ClassSat term paths := by
  constructor
  · rintro ⟨accepted, satisfied⟩; exact ⟨edit_sound graph root paths selected graph root term accepted, satisfied⟩
  · rintro ⟨accepted, satisfied⟩
    exact ⟨edit_preserves graph root paths active selected member graph root term accepted accepted satisfied, satisfied⟩

/-- Requiring one normalized class path cannot discard a term that satisfies the class. -/
theorem require_preserves (graph : Automaton State Symbol) (root : State) (paths : Class)
    (active : Nontrivial paths) (selected : Path) (member : selected ∈ paths)
    (term : Term Symbol) (accepted : Accepts graph root term) (satisfied : ClassSat term paths) :
    Accepts (PathFilter.restrict true graph) (root, PathFilter.pathPlan (fun _ => true) selected) term := by
  apply (PathFilter.require_exact graph root selected (fun _ => true) term).mpr
  obtain ⟨subtree, found⟩ := class_member_exists term paths active satisfied selected member
  exact ⟨accepted, subtree, found, rfl⟩

end MicroCFTA.EqualityNarrowing
