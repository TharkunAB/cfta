import MicroCFTA.ConstraintIndicators
import MicroCFTA.SignedUnion
import MicroCFTA.SymbolicCounterCache

/-!
# Concrete graph and guard semantics for the source counter

The signed source graph interface follows from constructor membership,
compiled guard semantics, and exact child-language intersection. No count
result or generated-intersection Boolean invariant is assumed.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Lattice (indicator)

/-- Constructor and ordered child membership before checking any guard. -/
def ShapeHolds (language : Nat → List (Term Symbol)) (edge : Edge Symbol) (term : Term Symbol) : Prop :=
  ∃ children, term = .node edge.symbol children ∧
    All₂ (fun node value => value ∈ language node) edge.children children

/-- Exact existence and equality meaning of a single path class. -/
noncomputable def classTest (term : Term Symbol) (paths : List (List Nat)) : Bool := by
  classical
  exact decide (Symbolic.ClassSatisfied term paths)

/-- The numeric interpretation of any edge, including intermediate signed intersections. -/
noncomputable def edgeValue (language : Nat → List (Term Symbol)) (term : Term Symbol) (edge : Edge Symbol) : Int := by
  classical
  exact indicator (decide (ShapeHolds language edge term)) * ConstraintIndicators.score (classTest term) edge.indicators

/-- Each raw equality component has constructor membership and its own conjunction. -/
theorem component_iff (language : Nat → List (Term Symbol)) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (term : Term Symbol) :
    term ∈ componentTerms language edge classes ↔
      ShapeHolds language edge term ∧ classes.all (classTest term) = true := by
  classical
  simp only [componentTerms_spec, ShapeHolds, List.all_eq_true, classTest, decide_eq_true_eq]
  constructor
  · rintro ⟨children, same, accepted, constraints⟩
    exact ⟨⟨children, same, accepted⟩, constraints⟩
  · rintro ⟨⟨children, same, accepted⟩, constraints⟩
    exact ⟨children, same, accepted, constraints⟩

/-- The literal source indicator sum has the complete numeric edge interpretation. -/
theorem component_score (language : Nat → List (Term Symbol)) (edge : Edge Symbol) (term : Term Symbol) :
    (edge.indicators.map fun (coefficient, classes) =>
      coefficient * indicator (@decide (term ∈ componentTerms language edge classes) (Classical.propDecidable _))).sum =
    edgeValue language term edge := by
  classical
  have each : ∀ classes, indicator (decide (term ∈ componentTerms language edge classes)) =
      indicator (decide (ShapeHolds language edge term)) * indicator (classes.all (classTest term)) := by
    intro classes
    rw [← Lattice.indicator_and]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simpa using component_iff language edge classes term
  simp only [edgeValue, ConstraintIndicators.score]
  induction edge.indicators with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.map_cons, List.sum_cons] at *
      rw [ih]
      grind

/-- Exact child-domain intersection preserves the ordered forest relation. -/
theorem child_intersection (language : Nat → List (Term Symbol)) (meet : Nat → Nat → Nat)
    (exact : ∀ left right term, term ∈ language (meet left right) ↔ term ∈ language left ∧ term ∈ language right)
    (left right : List Nat) (terms : List (Term Symbol)) (arity : left.length = right.length) :
    All₂ (fun node term => term ∈ language node) (List.zipWith meet left right) terms ↔
      All₂ (fun node term => term ∈ language node) left terms ∧
      All₂ (fun node term => term ∈ language node) right terms := by
  induction left generalizing right terms with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp arity.symm
      subst right
      constructor
      · intro accepted; exact ⟨accepted, accepted⟩
      · intro accepted; exact accepted.1
  | cons first rest ih =>
      cases right with
      | nil => simp at arity
      | cons other remaining =>
          have tails : rest.length = remaining.length := by simpa using arity
          constructor
          · intro accepted
            cases accepted with
            | cons head tail =>
                obtain ⟨a, b⟩ := (exact first other _).mp head
                obtain ⟨as, bs⟩ := (ih remaining _ tails).mp tail
                exact ⟨.cons a as, .cons b bs⟩
          · rintro ⟨leftAccepted, rightAccepted⟩
            cases leftAccepted with
            | cons head tail =>
                cases rightAccepted with
                | cons otherHead otherTail =>
                    exact .cons ((exact first other _).mpr ⟨head, otherHead⟩)
                      ((ih remaining _ tails).mpr ⟨tail, otherTail⟩)

/-- Two constructor interpretations can overlap only when labels and arities match. -/
theorem shape_matching (language : Nat → List (Term Symbol)) (left right : Edge Symbol) (term : Term Symbol)
    (first : ShapeHolds language left term) (second : ShapeHolds language right term) :
    left.symbol = right.symbol ∧ left.children.length = right.children.length := by
  obtain ⟨children, same, first⟩ := first
  obtain ⟨others, equal, second⟩ := second
  have paired := Term.node.inj (same.symm.trans equal)
  exact ⟨paired.1, first.length_eq.trans (congrArg List.length paired.2 |>.trans second.length_eq.symm)⟩

/-- The constructed intersection edge has exactly both constructor interpretations. -/
theorem shape_intersection (language : Nat → List (Term Symbol)) (graph : Graph Symbol)
    (exact : ∀ left right term, term ∈ language (graph.intersect left right) ↔ term ∈ language left ∧ term ∈ language right)
    (left right : Edge Symbol) (same : left.symbol = right.symbol)
    (arity : left.children.length = right.children.length) (term : Term Symbol) (indicators) :
    ShapeHolds language ⟨left.symbol, List.zipWith graph.intersect left.children right.children, indicators⟩ term ↔
      ShapeHolds language left term ∧ ShapeHolds language right term := by
  constructor
  · rintro ⟨children, form, accepted⟩
    obtain ⟨first, second⟩ := (child_intersection language graph.intersect exact left.children right.children children arity).mp accepted
    exact ⟨⟨children, form, first⟩, ⟨children, by rw [← same]; exact form, second⟩⟩
  · rintro ⟨⟨children, form, first⟩, ⟨others, equal, second⟩⟩
    have childrenSame := (Term.node.inj (form.symm.trans equal)).2
    subst others
    exact ⟨children, form, (child_intersection language graph.intersect exact left.children right.children children arity).mpr ⟨first, second⟩⟩

/-- Source intersection multiplies numeric edge interpretations for every edge record. -/
theorem edgeValue_intersection [DecidableEq Symbol] (language : Nat → List (Term Symbol)) (graph : Graph Symbol)
    (exact : ∀ left right term, term ∈ language (graph.intersect left right) ↔ term ∈ language left ∧ term ∈ language right)
    (term : Term Symbol) : SignedUnion.ExactProduct (edgeValue language term) (intersectEdge graph) := by
  classical
  intro left right
  by_cases matching : left.symbol = right.symbol ∧ left.children.length = right.children.length
  · simp only [intersectEdge, ite_eq_left matching]
    have shape := shape_intersection language graph exact left right matching.1 matching.2 term
      (ConstraintIndicators.conjoin left.indicators right.indicators)
    have boolean : decide (ShapeHolds language
        ⟨left.symbol, List.zipWith graph.intersect left.children right.children,
          ConstraintIndicators.conjoin left.indicators right.indicators⟩ term) =
        (decide (ShapeHolds language left term) && decide (ShapeHolds language right term)) := by
      apply Bool.eq_iff_iff.mpr
      simpa using shape
    change indicator (decide (ShapeHolds language
        ⟨left.symbol, List.zipWith graph.intersect left.children right.children,
          ConstraintIndicators.conjoin left.indicators right.indicators⟩ term)) *
        ConstraintIndicators.score (classTest term) (ConstraintIndicators.conjoin left.indicators right.indicators) = _
    rw [boolean, ConstraintIndicators.score_conjoin, Lattice.indicator_and]
    simp only [edgeValue]
    grind
  · simp only [intersectEdge, ite_eq_right matching]
    have absent : ¬ (ShapeHolds language left term ∧ ShapeHolds language right term) :=
      fun both => matching (shape_matching language left right term both.1 both.2)
    rcases Decidable.not_and_iff_or_not.mp absent with absent | absent <;>
      simp [edgeValue, absent, indicator]

/-- Exact original guards and graph rows derive the entire nested signed node indicator. -/
theorem expansion_indicators [DecidableEq Symbol] (language : Nat → List (Term Symbol)) (graph : Graph Symbol)
    (intersection : ∀ left right term, term ∈ language (graph.intersect left right) ↔ term ∈ language left ∧ term ∈ language right)
    (guard : Edge Symbol → Term Symbol → Bool)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = indicator (guard edge term))
    (rows : ∀ node term, term ∈ language node ↔
      ∃ edge ∈ graph.edges node, ShapeHolds language edge term ∧ guard edge term = true)
    (node : Nat) (term : Term Symbol) :
    Symbolic.weighted
      (fun component => indicator (@decide (term ∈ componentTerms language component.1 component.2) (Classical.propDecidable _)))
      (expansionPieces graph node) = indicator (@decide (term ∈ language node) (Classical.propDecidable _)) := by
  classical
  rw [expansionPieces_weighted graph node (fun edge classes => indicator (@decide (term ∈ componentTerms language edge classes) (Classical.propDecidable _)))]
  have values : Symbolic.weighted
      (fun edge => (edge.indicators.map fun (coefficient, classes) =>
        coefficient * indicator (@decide (term ∈ componentTerms language edge classes) (Classical.propDecidable _))).sum)
      (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) =
      Symbolic.weighted (edgeValue language term)
      (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) := by
    apply weighted_congr
    intro edge _
    exact component_score language edge.1 term
  rw [values]
  let member := fun edge => decide (ShapeHolds language edge term) && guard edge term
  have original : ∀ edge ∈ graph.edges node, edgeValue language term edge = indicator (member edge) := by
    intro edge present
    rw [edgeValue, compiled node edge present term]
    exact (Lattice.indicator_and _ _).symm
  rw [SignedUnion.union_indicator (edgeValue language term) member (intersectEdge graph)
    (edgeValue_intersection language graph intersection term) (graph.edges node) original]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa [member, List.any_eq_true] using (rows node term).symm

/-- Build the complete source counter semantics from independent guarded graph rows. -/
noncomputable def counterMeaningFromRows [DecidableEq Symbol] (graph : Graph Symbol)
    (language : Nat → List (Term Symbol)) (distinct : ∀ node, (language node).Nodup)
    (intersection : ∀ left right term, term ∈ language (graph.intersect left right) ↔ term ∈ language left ∧ term ∈ language right)
    (guard : Edge Symbol → Term Symbol → Bool)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = indicator (guard edge term))
    (rows : ∀ node term, term ∈ language node ↔
      ∃ edge ∈ graph.edges node, ShapeHolds language edge term ∧ guard edge term = true) : CounterMeaning graph :=
  ⟨language, distinct, intersection, expansion_indicators language graph intersection guard compiled rows⟩

end MicroCFTA.SymbolicDriver
