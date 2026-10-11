import MicroCFTA.SymbolicBijections

/-!
# Exact finite counts for whole-variable unification

The source intersects two domains and retains one shared live variable.
The eliminated variable becomes a binding. This module proves that the
rewrite preserves the number of distinct live solutions, including all
other pending constraints.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Satisfies)

/-- Stable distinct keys identify exactly one stored domain. -/
theorem entry_of_same_key (entries : List (Nat × Value)) (distinct : (entries.map Prod.fst).Nodup)
    (name : Nat) (value : Value) (stored : (name, value) ∈ entries)
    (entry : Nat × Value) (member : entry ∈ entries) (sameKey : entry.1 = name) : entry = (name, value) := by
  have expected := lookup_of_member entries distinct name value stored
  have actual := lookup_of_member entries distinct entry.1 entry.2 member
  rw [sameKey] at actual
  exact Prod.ext sameKey (Option.some.inj (actual.symm.trans expected))

/-- Whole-variable equality requires one existing value shared by both variables. -/
theorem variable_equality_iff (assignment : Nat → Term Symbol) (left right : Nat) :
    Satisfies assignment (.equal ⟨.var left, []⟩ ⟨.var right, []⟩) ↔ assignment left = assignment right := by
  simp only [Satisfies, Symbolic.targetValue, Symbolic.instantiate, Term.atPath]
  constructor
  · rintro ⟨term, first, second⟩
    exact Option.some.inj (first.trans second.symm)
  · intro same
    exact ⟨assignment right, congrArg some same, rfl⟩

/-- The source's exact domain and binding update for distinct whole variables. -/
def mergedProblem (problem : Problem Symbol) (left right common : Nat) : Problem Symbol :=
  {problem with
    domains := insert (delete problem.domains left) right common
    bindings := insert problem.bindings left (.var right)}

/-- Restore the equation passed separately to the source unifier. -/
def variableEquation (problem : Problem Symbol) (left right : Nat) : Problem Symbol :=
  {problem with obligations := .equal ⟨.var left, []⟩ ⟨.var right, []⟩ :: problem.obligations}

/-- The merged binding is exactly the old whole-variable equality. -/
theorem merged_binding_iff (problem : Problem Symbol) (empty : problem.bindings = [])
    (left right common : Nat) (assignment : Nat → Term Symbol) :
    BindingsHold assignment (mergedProblem problem left right common).bindings ↔ assignment left = assignment right := by
  simp [mergedProblem, empty, insert, delete, BindingsHold, Symbolic.instantiate]

/-- A different original domain remains in the merged map; the representative key is replaced. -/
theorem merged_domain_member (problem : Problem Symbol) (left right common : Nat)
    (entry : Nat × Nat) (member : entry ∈ problem.domains) (notLeft : entry.1 ≠ left) (notRight : entry.1 ≠ right) :
    entry ∈ (mergedProblem problem left right common).domains := by
  apply (insert_member (delete problem.domains left) right common entry).mpr
  exact Or.inr ⟨by simp [delete, member, notLeft], notRight⟩

/-- The intersected representative domain is present after the source update. -/
theorem merged_common_member (problem : Problem Symbol) (left right common : Nat) :
    (right, common) ∈ (mergedProblem problem left right common).domains :=
  (insert_member (delete problem.domains left) right common (right, common)).mpr (Or.inl rfl)

/-- Exact domain intersection makes the source's original and merged valuation predicates equivalent. -/
theorem merged_solution_iff (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (empty : problem.bindings = [])
    (left right leftNode rightNode common : Nat)
    (leftMember : (left, leftNode) ∈ problem.domains) (rightMember : (right, rightNode) ∈ problem.domains)
    (intersection : ∀ term, term ∈ language common ↔ term ∈ language leftNode ∧ term ∈ language rightNode)
    (assignment : Nat → Term Symbol) :
    ProblemHolds (fun node term => term ∈ language node) assignment (variableEquation problem left right) ↔
      ProblemHolds (fun node term => term ∈ language node) assignment (mergedProblem problem left right common) := by
  constructor
  · rintro ⟨domains, _, constraints⟩
    have shared := (variable_equality_iff assignment left right).mp
      (constraints (.equal ⟨.var left, []⟩ ⟨.var right, []⟩) (by simp [variableEquation]))
    refine ⟨?_, (merged_binding_iff problem empty left right common assignment).mpr shared, ?_⟩
    · intro entry member
      rcases (insert_member (delete problem.domains left) right common entry).mp member with rfl | old
      · apply (intersection (assignment right)).mpr
        exact ⟨by simpa only [shared] using domains (left, leftNode) leftMember, domains (right, rightNode) rightMember⟩
      · exact domains entry (List.mem_filter.mp old.1).1
    · intro obligation member
      exact constraints obligation (List.mem_cons_of_mem _ member)
  · rintro ⟨domains, bindings, constraints⟩
    have shared := (merged_binding_iff problem empty left right common assignment).mp bindings
    have commonValue := (intersection (assignment right)).mp
      (domains (right, common) (merged_common_member problem left right common))
    refine ⟨?_, ?_, ?_⟩
    · intro entry member
      by_cases atLeft : entry.1 = left
      · have same := entry_of_same_key problem.domains distinct left leftNode leftMember entry member atLeft
        subst entry
        simpa only [shared] using commonValue.1
      · by_cases atRight : entry.1 = right
        · have same := entry_of_same_key problem.domains distinct right rightNode rightMember entry member atRight
          subst entry
          exact commonValue.2
        · exact domains entry (merged_domain_member problem left right common entry member atLeft atRight)
    · simp [variableEquation, BindingsHold, empty]
    · intro obligation member
      rcases List.mem_cons.mp member with rfl | old
      · exact (variable_equality_iff assignment left right).mpr shared
      · exact constraints obligation old

/-- Every old live value is fixed by the merged live tuple and the retained equality binding. -/
theorem merged_determines_original (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (left right common : Nat) (first second : Nat → Term Symbol)
    (firstValid : ProblemHolds (fun node term => term ∈ language node) first (variableEquation problem left right))
    (secondValid : ProblemHolds (fun node term => term ∈ language node) second (variableEquation problem left right))
    (same : ∀ entry ∈ (mergedProblem problem left right common).domains, first entry.1 = second entry.1) :
    ∀ entry ∈ problem.domains, first entry.1 = second entry.1 := by
  have firstShared := (variable_equality_iff first left right).mp
    (firstValid.2.2 (.equal ⟨.var left, []⟩ ⟨.var right, []⟩) (by simp [variableEquation]))
  have secondShared := (variable_equality_iff second left right).mp
    (secondValid.2.2 (.equal ⟨.var left, []⟩ ⟨.var right, []⟩) (by simp [variableEquation]))
  have atRight := same (right, common) (merged_common_member problem left right common)
  intro entry member
  by_cases isLeft : entry.1 = left
  · simpa only [isLeft, firstShared, secondShared] using atRight
  · by_cases isRight : entry.1 = right
    · simpa only [isRight] using atRight
    · exact same entry (merged_domain_member problem left right common entry member isLeft isRight)

/-- The original tuple records every name that survives the merge. -/
theorem original_determines_merged (problem : Problem Symbol) (left right rightNode common : Nat)
    (rightMember : (right, rightNode) ∈ problem.domains) (first second : Nat → Term Symbol)
    (same : ∀ entry ∈ problem.domains, first entry.1 = second entry.1) :
    ∀ entry ∈ (mergedProblem problem left right common).domains, first entry.1 = second entry.1 := by
  intro entry member
  rcases (insert_member (delete problem.domains left) right common entry).mp member with rfl | old
  · exact same (right, rightNode) rightMember
  · exact same entry (List.mem_filter.mp old.1).1

/-- Whole-variable unification preserves the exact finite count, including correlated residual constraints. -/
theorem unify_variables_count (language : Nat → List (Term Symbol))
    (languageDistinct : ∀ node, (language node).Nodup) (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (empty : problem.bindings = [])
    (left right leftNode rightNode common : Nat)
    (leftMember : (left, leftNode) ∈ problem.domains) (rightMember : (right, rightNode) ∈ problem.domains)
    (intersection : ∀ term, term ∈ language common ↔ term ∈ language leftNode ∧ term ∈ language rightNode) :
    solutionCount language (variableEquation problem left right) = solutionCount language (mergedProblem problem left right common) := by
  apply solutionCount_equivalent language languageDistinct
    (variableEquation problem left right) (mergedProblem problem left right common)
  · exact merged_solution_iff language problem distinct empty left right leftNode rightNode common leftMember rightMember intersection
  · exact merged_determines_original language problem left right common
  · intro first second _ _ same
    exact original_determines_merged problem left right rightNode common rightMember first second same

end MicroCFTA.SymbolicDriver
