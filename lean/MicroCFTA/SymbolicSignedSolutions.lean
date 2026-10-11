import MicroCFTA.SymbolicExpansion

/-!
# Signed expansion counts over correlated finite solutions

A source guard indicator is a signed sum of equality components. The proof
below lifts its pointwise term identity to the finite count of complete live
tuples. Other coordinates and all pending constraints remain unchanged.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (weighted totalOver Coefficients)
open Lattice (indicator)
noncomputable section
local instance : DecidableEq (Term Symbol) := Classical.typeDecidableEq _

/-- Zero component values have zero signed total. -/
theorem weighted_zero (entries : Coefficients Piece) : weighted (fun _ => 0) entries = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [weighted, Int.mul_zero, Int.zero_add, ih]

/-- Equal interpretations on the stored keys give equal signed sums. -/
theorem weighted_congr (first second : Piece → Int) (entries : Coefficients Piece)
    (same : ∀ entry ∈ entries, first entry.1 = second entry.1) : weighted first entries = weighted second entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [weighted, weighted, same entry (by simp), ih (fun other member => same other (by simp [member]))]

/-- A containing finite distinct list counts the exact members of a smaller distinct list. -/
theorem support_counts [DecidableEq Value] (support values : List Value) (supportDistinct : support.Nodup)
    (valuesDistinct : values.Nodup) (included : values ⊆ support) :
    totalOver support (fun value => indicator (decide (value ∈ values))) = (values.length : Int) := by
  classical
  rw [totalOver_indicator]
  congr 1
  apply Nat.le_antisymm
  · exact List.Nodup.length_le_of_subset (supportDistinct.filter _) (by
      intro value member
      exact of_decide_eq_true (List.mem_filter.mp member).2)
  · exact List.Nodup.length_le_of_subset valuesDistinct (by
      intro value member
      exact List.mem_filter.mpr ⟨included member, by simp [member]⟩)

/-- A pointwise signed membership identity implies exact cardinality, including negative components. -/
theorem signed_lengths [DecidableEq Value] (languages : Piece → List Value) (entries : Coefficients Piece) (result : List Value)
    (distinct : ∀ key, (languages key).Nodup) (resultDistinct : result.Nodup)
    (exact : ∀ value, weighted (fun key => indicator (decide (value ∈ languages key))) entries =
      indicator (decide (value ∈ result))) :
    weighted (fun key => ((languages key).length : Int)) entries = (result.length : Int) := by
  classical
  let support := (result ++ entries.flatMap (fun entry => languages entry.1)).eraseDups
  have supportDistinct : support.Nodup := eraseDups_nodup _
  have resultIncluded : result ⊆ support := by
    intro value member
    simp only [support, List.mem_eraseDups, List.mem_append]
    exact Or.inl member
  have componentIncluded : ∀ entry ∈ entries, languages entry.1 ⊆ support := by
    intro entry member value present
    simp only [support, List.mem_eraseDups, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨entry, member, present⟩)
  calc
    weighted (fun key => ((languages key).length : Int)) entries =
        weighted (fun key => totalOver support (fun value => indicator (decide (value ∈ languages key)))) entries :=
      weighted_congr _ _ entries (fun entry member =>
        (support_counts support (languages entry.1) supportDistinct (distinct entry.1) (componentIncluded entry member)).symm)
    _ = totalOver support (fun value => weighted (fun key => indicator (decide (value ∈ languages key))) entries) :=
      Symbolic.weighted_totalOver support _ entries
    _ = totalOver support (fun value => indicator (decide (value ∈ result))) := by
      unfold totalOver
      congr 1
      exact List.map_congr_left (fun value _ => exact value)
    _ = (result.length : Int) := support_counts support result supportDistinct resultDistinct resultIncluded

/-- Replace only one variable's candidate language and retain all logical requirements. -/
noncomputable def coordinateSolutions (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name : Nat) (terms : List (Term Symbol)) : List (List (Term Symbol)) := by
  classical
  exact (products (fun entry => if entry.1 = name then terms else language entry.2) problem.domains).filter
    fun values => decide (LiveSolution problem values)

/-- Distinct coordinate languages give distinct tuples after logical filtering. -/
theorem coordinateSolutions_nodup (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (problem : Problem Symbol) (name : Nat)
    (terms : List (Term Symbol)) (termsDistinct : terms.Nodup) :
    (coordinateSolutions language problem name terms).Nodup := by
  classical
  apply List.Pairwise.filter
  apply products_nodup
  intro entry _
  split
  · exact termsDistinct
  · exact distinct entry.2

/-- A logically valid tuple tests a replacement domain at its selected value exactly once. -/
theorem coordinateSolutions_fixed (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name node : Nat) (selected : (name, node) ∈ problem.domains) (terms : List (Term Symbol))
    (assignment : Nat → Term Symbol) (values : List (Term Symbol))
    (matching : TupleMatches assignment problem.domains values) (live : LiveSolution problem values) :
    values ∈ coordinateSolutions language problem name terms ↔
      (∀ entry ∈ problem.domains, entry.1 ≠ name → assignment entry.1 ∈ language entry.2) ∧ assignment name ∈ terms := by
  classical
  simp only [coordinateSolutions, List.mem_filter, decide_eq_true_eq, live, and_true,
    matching_products_iff _ assignment problem.domains values matching]
  constructor
  · intro holds
    constructor
    · intro entry member other
      simpa only [ite_eq_right other] using holds entry member
    · simpa only [ite_true] using holds (name, node) selected
  · rintro ⟨remaining, selectedValue⟩ entry member
    split
    · rename_i same
      simpa only [same] using selectedValue
    · exact remaining entry member ‹entry.1 ≠ name›

/-- The original candidate domains split into the selected domain and every other live domain. -/
theorem originalSolutions_fixed (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup)
    (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (assignment : Nat → Term Symbol) (values : List (Term Symbol))
    (matching : TupleMatches assignment problem.domains values) (live : LiveSolution problem values) :
    values ∈ solutionTuples language problem ↔
      (∀ entry ∈ problem.domains, entry.1 ≠ name → assignment entry.1 ∈ language entry.2) ∧ assignment name ∈ language node := by
  classical
  simp only [solutionTuples, List.mem_filter, decide_eq_true_eq, live, and_true,
    matching_candidate_iff language assignment problem.domains values matching]
  constructor
  · intro holds
    exact ⟨fun entry member _ => holds entry member, holds (name, node) selected⟩
  · rintro ⟨remaining, selectedValue⟩ entry member
    by_cases same : entry.1 = name
    · have equal := entry_of_same_key problem.domains distinct name node selected entry member same
      subst entry
      exact selectedValue
    · exact remaining entry member same

/-- Signed selected-value membership lifts through all independent domains and correlated constraints. -/
theorem coordinate_indicator [DecidableEq Symbol] (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup)
    (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (components : Piece → List (Term Symbol)) (entries : Coefficients Piece)
    (exact : ∀ term, weighted (fun key => indicator (decide (term ∈ components key))) entries =
      indicator (decide (term ∈ language node))) (values : List (Term Symbol)) :
    weighted (fun key => indicator (decide (values ∈ coordinateSolutions language problem name (components key)))) entries =
      indicator (decide (values ∈ solutionTuples language problem)) := by
  classical
  by_cases live : LiveSolution problem values
  · obtain ⟨assignment, matching, bindings, constraints⟩ := live
    have live : LiveSolution problem values := ⟨assignment, matching, bindings, constraints⟩
    have original := originalSolutions_fixed language problem distinct name node selected assignment values matching live
    have component := fun key => coordinateSolutions_fixed language problem name node selected (components key) assignment values matching live
    by_cases remaining : ∀ entry ∈ problem.domains, entry.1 ≠ name → assignment entry.1 ∈ language entry.2
    · have same : ∀ key, (values ∈ coordinateSolutions language problem name (components key)) ↔ assignment name ∈ components key := by
        intro key
        exact ⟨fun member => ((component key).mp member).2, fun member => (component key).mpr ⟨remaining, member⟩⟩
      have originalSame : (values ∈ solutionTuples language problem) ↔ assignment name ∈ language node := by
        exact ⟨fun member => (original.mp member).2, fun member => original.mpr ⟨remaining, member⟩⟩
      simpa only [same, originalSame] using exact (assignment name)
    · have same : ∀ key, ¬values ∈ coordinateSolutions language problem name (components key) := by
        intro key member
        exact remaining ((component key).mp member).1
      have originalAbsent : ¬values ∈ solutionTuples language problem := fun member => remaining (original.mp member).1
      simp only [same, decide_false, indicator, originalAbsent, Bool.false_eq_true, ite_false]
      exact weighted_zero entries
  · have same : ∀ key, ¬values ∈ coordinateSolutions language problem name (components key) := by
      intro key member
      exact live (of_decide_eq_true (List.mem_filter.mp member).2)
    have originalAbsent : ¬values ∈ solutionTuples language problem := by
      intro member
      exact live (of_decide_eq_true (List.mem_filter.mp member).2)
    simp only [same, decide_false, indicator, originalAbsent, Bool.false_eq_true, ite_false]
    exact weighted_zero entries

/-- Exact signed selected-domain membership yields the exact complete solution count. -/
theorem signed_coordinate_count [DecidableEq Symbol] (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (problem : Problem Symbol)
    (namesDistinct : (problem.domains.map Prod.fst).Nodup)
    (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (components : Piece → List (Term Symbol)) (componentDistinct : ∀ key, (components key).Nodup)
    (entries : Coefficients Piece)
    (exact : ∀ term, weighted (fun key => indicator (decide (term ∈ components key))) entries =
      indicator (decide (term ∈ language node))) :
    weighted (fun key => ((coordinateSolutions language problem name (components key)).length : Int)) entries =
      (solutionCount language problem : Int) := by
  apply signed_lengths (fun key => coordinateSolutions language problem name (components key)) entries (solutionTuples language problem)
    (fun key => coordinateSolutions_nodup language distinct problem name (components key) (componentDistinct key))
    (solutionTuples_nodup language distinct problem)
  intro value
  simpa only [indicator, decide_eq_true_eq] using
    coordinate_indicator language problem namesDistinct name node selected components entries exact value

/-- The source's two signed loops flattened without changing coefficient order. -/
def expansionPieces [DecidableEq Symbol] (graph : Graph Symbol) (node : Nat) :
    Coefficients (Edge Symbol × List (List (List Nat))) :=
  (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)).flatMap fun (edge, outer) =>
    edge.indicators.map fun (inner, classes) => ((edge, classes), outer * inner)

/-- One scaled source indicator loop has the same value before and after flattening. -/
theorem weighted_component_loop (value : Piece → Int) (outer : Int) (components : List (Int × Piece)) :
    weighted value (components.map fun (inner, piece) => (piece, outer * inner)) =
      outer * (components.map fun (inner, piece) => inner * value piece).sum := by
  induction components with
  | nil => simp only [List.map_nil, weighted, List.sum_nil, Int.mul_zero]
  | cons component rest ih =>
      rcases component with ⟨inner, piece⟩
      simp only [List.map_cons, weighted, List.sum_cons, ih, Int.mul_add, Int.mul_assoc]

/-- Flattening the union and guard loops preserves the actual nested signed count expression. -/
theorem expansionPieces_weighted [DecidableEq Symbol] (graph : Graph Symbol) (node : Nat)
    (value : Edge Symbol → List (List (List Nat)) → Int) :
    weighted (fun component => value component.1 component.2) (expansionPieces graph node) =
      weighted (fun edge => (edge.indicators.map fun (coefficient, classes) => coefficient * value edge classes).sum)
        (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) := by
  unfold expansionPieces
  generalize Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node) = edges
  induction edges with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨edge, outer⟩
      rw [List.flatMap_cons, Symbolic.weighted_append, weighted, ih]
      congr 1
      dsimp only
      generalize edge.indicators = components
      induction components with
      | nil => simp only [List.map_nil, weighted, List.sum_nil, Int.mul_zero]
      | cons component components ih =>
          rcases component with ⟨inner, classes⟩
          simp only [List.map_cons, weighted, List.sum_cons, ih, Int.mul_add, Int.mul_assoc]

/-- Exact term indicators close the source's complete signed variable-expansion count. -/
theorem expand_variable_count [DecidableEq Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (distinct : ∀ node, (language node).Nodup)
    (problem : Problem Symbol) (namesDistinct : (problem.domains.map Prod.fst).Nodup)
    (empty : problem.bindings = []) (within : ProblemScoped problem)
    (fresh : ∀ entry ∈ problem.domains, entry.1 < problem.nextVariable)
    (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (exact : ∀ term, weighted (fun component => indicator (decide (term ∈ componentTerms language component.1 component.2)))
        (expansionPieces graph node) = indicator (decide (term ∈ language node))) :
    weighted (fun edge => (edge.indicators.map fun (coefficient, classes) =>
        coefficient * (solutionCount language (expandedProblem problem name edge classes) : Int)).sum)
      (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) = (solutionCount language problem : Int) := by
  rw [← expansionPieces_weighted graph node (fun edge classes => (solutionCount language (expandedProblem problem name edge classes) : Int))]
  have count := signed_coordinate_count language distinct problem namesDistinct name node selected
    (fun component : Edge Symbol × List (List (List Nat)) => componentTerms language component.1 component.2)
    (fun component => componentTerms_nodup language distinct component.1 component.2) (expansionPieces graph node) exact
  calc
    weighted (fun component => (solutionCount language (expandedProblem problem name component.1 component.2) : Int))
        (expansionPieces graph node) =
      weighted (fun component => ((componentSolutions language problem name component.1 component.2).length : Int))
        (expansionPieces graph node) := by
          apply weighted_congr
          intro entry _
          rw [expand_component_count language distinct problem empty within fresh name node selected entry.1.1 entry.1.2]
    _ = (solutionCount language problem : Int) := count

end
end MicroCFTA.SymbolicDriver
