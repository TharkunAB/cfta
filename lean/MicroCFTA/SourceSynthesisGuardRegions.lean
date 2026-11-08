import MicroCFTA.SourceSynthesisFirstOrderConstruction
import MicroCFTA.EqualityNormalizeRightIdeal

/-!
# Type-field endpoint regions for actual synthesis layouts

These predicates describe source row occurrences. They do not infer a role
from a symbol. Every path belongs to the Type phase. This fact supplies no
decreasing measure for Type execution.
-/
namespace MicroCFTA.SourceSynthesisGuardRegions
open EqualityNormalize
open SourceSynthesisTypeSyntax (Ty)
open SourceSynthesisGeneralizeSyntax (Guard eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression component application ofType)
open InternedNestedConstruction (Syntax EdgeSyntax)

/-- A program annotation occupies child zero. -/
def annotationRegion (path : Path) : Prop := [0].IsPrefix path

/-- A component row has the program annotation layout. -/
abbrev componentRegion := annotationRegion

/-- Application has two direct Type fields and two program annotations. -/
def applicationRegion (path : Path) : Prop :=
  [0].IsPrefix path ∨ [1].IsPrefix path ∨ [2, 0].IsPrefix path ∨ [3, 0].IsPrefix path

/-- Filter has the goal Type field and the candidate program annotation. -/
def filterRegion (path : Path) : Prop :=
  [0].IsPrefix path ∨ [1, 0].IsPrefix path

/-- The Type phase permits every path, including the root path. -/
def typeRegion (_path : Path) : Prop := True

private theorem prefix_right (root path : Path) (included : root.IsPrefix path) (suffix : Path) :
    root.IsPrefix (path ++ suffix) := by
  obtain ⟨rest, rfl⟩ := included
  exact ⟨rest ++ suffix, by simp only [List.append_assoc]⟩

/-- Appending a suffix stays inside the annotation field. -/
theorem annotation_rightClosed :
    ∀ path, annotationRegion path → ∀ suffix, annotationRegion (path ++ suffix) := by
  intro path included suffix
  exact prefix_right [0] path included suffix

/-- Component Type fields are closed under right extension. -/
theorem component_rightClosed :
    ∀ path, componentRegion path → ∀ suffix, componentRegion (path ++ suffix) := annotation_rightClosed

/-- Application Type fields are closed under right extension. -/
theorem application_rightClosed :
    ∀ path, applicationRegion path → ∀ suffix, applicationRegion (path ++ suffix) := by
  intro path included suffix
  rcases included with first | second | third | fourth
  · exact Or.inl (prefix_right [0] path first suffix)
  · exact Or.inr (Or.inl (prefix_right [1] path second suffix))
  · exact Or.inr (Or.inr (Or.inl (prefix_right [2, 0] path third suffix)))
  · exact Or.inr (Or.inr (Or.inr (prefix_right [3, 0] path fourth suffix)))

/-- Filter Type fields are closed under right extension. -/
theorem filter_rightClosed :
    ∀ path, filterRegion path → ∀ suffix, filterRegion (path ++ suffix) := by
  intro path included suffix
  rcases included with first | second
  · exact Or.inl (prefix_right [0] path first suffix)
  · exact Or.inr (prefix_right [1, 0] path second suffix)

/-- The unrestricted Type phase is closed under right extension. -/
theorem type_rightClosed :
    ∀ path, typeRegion path → ∀ suffix, typeRegion (path ++ suffix) := by
  intros
  trivial

/-- Descent to the function program leaves exactly its annotation region. -/
theorem application_descend_function (path : Path) :
    applicationRegion (2 :: path) ↔ annotationRegion path := by
  simp [applicationRegion, annotationRegion, List.cons_prefix_cons]

/-- Descent to the argument program leaves exactly its annotation region. -/
theorem application_descend_argument (path : Path) :
    applicationRegion (3 :: path) ↔ annotationRegion path := by
  simp [applicationRegion, annotationRegion, List.cons_prefix_cons]

/-- Descent to the filter's program leaves exactly its annotation region. -/
theorem filter_descend_program (path : Path) :
    filterRegion (1 :: path) ↔ annotationRegion path := by
  simp [filterRegion, annotationRegion, List.cons_prefix_cons]

/-- The Top residual takes the actual accessor's empty fast path. -/
theorem eqGuard_accessor (classes : Constraints) :
    SourceCompactGuards.sourceEqualities (eqGuard classes) = (eqGuard classes).equalities := rfl

private theorem eqGuard_region (P : Path → Prop)
    (rightClosed : ∀ path, P path → ∀ suffix, P (path ++ suffix))
    (classes : Constraints) (inputs : ∀ path ∈ members classes, P path) :
    ∀ path ∈ members ((eqGuard classes).equalities.getD []), P path := by
  intro path member
  cases computed : SourceCompactGuards.normalize classes with
  | none =>
      simp [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source, computed, members] at member
  | some output =>
      have included : path ∈ members output := by
        simpa only [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source, computed, Option.getD] using member
      exact EqualityNormalizeRightIdeal.normalize_preserves P rightClosed classes output inputs computed path included

private theorem application_inputs :
    ∀ path ∈ members [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]], applicationRegion path := by
  intro path member
  simp [members] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [applicationRegion, List.cons_prefix_cons]

private theorem filter_inputs :
    ∀ path ∈ members [[[0], [1, 0]]], filterRegion path := by
  intro path member
  simp [members] at member
  rcases member with rfl | rfl <;> simp [filterRegion, List.cons_prefix_cons]

/-- Every actual component guard endpoint is in its annotation region. -/
theorem component_guard_endpoints (types : Expression) (name : String) (typ : Ty)
    (symbol : String) (guard : Guard) (children : List Expression)
    (actual : component types name typ = .mk symbol guard children) :
    (∀ path ∈ members (guard.equalities.getD []), componentRegion path) ∧
      (∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), componentRegion path) := by
  cases actual
  have stored : ∀ path ∈ members (SourceSynthesisGeneralizeSyntax.top.equalities.getD []), componentRegion path := by
    intro path member
    simp [SourceSynthesisGeneralizeSyntax.top, SourceEqualityConstraintConstructors.top,
      members] at member
  exact ⟨stored, stored⟩

/-- Actual application guards retain only endpoints in the application Type fields. -/
theorem application_guard_endpoints (types function argument : Expression)
    (symbol : String) (guard : Guard) (children : List Expression)
    (actual : application types function argument = .node [.mk symbol guard children]) :
    (∀ path ∈ members (guard.equalities.getD []), applicationRegion path) ∧
      (∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), applicationRegion path) := by
  cases actual
  have stored := eqGuard_region applicationRegion application_rightClosed
    [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] application_inputs
  exact ⟨stored, by simpa only [eqGuard_accessor] using stored⟩

/-- Actual filter guards retain only endpoints in the filter Type fields. -/
theorem filter_guard_endpoints (candidates goal : Expression)
    (symbol : String) (guard : Guard) (children : List Expression)
    (actual : ofType candidates goal = .node [.mk symbol guard children]) :
    (∀ path ∈ members (guard.equalities.getD []), filterRegion path) ∧
      (∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), filterRegion path) := by
  cases actual
  have stored := eqGuard_region filterRegion filter_rightClosed [[[0], [1, 0]]] filter_inputs
  exact ⟨stored, by simpa only [eqGuard_accessor] using stored⟩

end MicroCFTA.SourceSynthesisGuardRegions
