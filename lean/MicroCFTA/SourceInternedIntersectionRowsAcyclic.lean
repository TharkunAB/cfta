import MicroCFTA.SourceInternedIntersectionRowsLanguage

/-!
# Finite ordinary intersection with derived recursive correctness

The worker executes the ordinary source branch recursively through actual
edge and node caches. Fuel bounds descent through the left operand's stored
ordinary rows. A structural-size bound exists for every finite record. This
is the ordinary construction kernel. Source memo dispatch, operand ordering,
and recursive binder exposure remain separate correspondence obligations.
-/
namespace MicroCFTA.SourceInternedIntersectionRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency Language

/-- A finite bound on descent through stored ordinary child records. -/
def Bounded : Nat → Value Symbol Unit → Prop
  | 0, value => nodeEdges value = []
  | fuel + 1, value => ∀ edge ∈ nodeEdges value, ∀ child ∈ edge.children, Bounded fuel child

/-- Every direct ordinary child has a strictly smaller immutable record. -/
theorem child_smaller (value : Value Symbol Unit) (edge : EdgeValue Symbol Unit)
    (member : edge ∈ nodeEdges value) (child : Value Symbol Unit) (inside : child ∈ edge.children) :
    sizeOf child < sizeOf value := by
  cases value <;> simp only [nodeEdges] at member <;> try contradiction
  case node entry edges depth free =>
    have outer := List.sizeOf_lt_of_mem member
    have inner := List.sizeOf_lt_of_mem inside
    cases edge
    simp only [EdgeValue.children] at inner
    simp only [EdgeValue.mk.sizeOf_spec] at outer
    simp only [Value.node.sizeOf_spec]
    omega

/-- The concrete record size supplies a sufficient finite descent bound. -/
theorem bounded_size (fuel : Nat) (value : Value Symbol Unit) (large : sizeOf value ≤ fuel) : Bounded fuel value := by
  induction fuel generalizing value with
  | zero =>
      cases value <;> simp_all [Value.empty.sizeOf_spec, Value.reference.sizeOf_spec, Value.node.sizeOf_spec,
        Value.union.sizeOf_spec, Value.mu.sizeOf_spec]
  | succ fuel ih =>
      intro edge member child inside
      exact ih child (by have smaller := child_smaller value edge member child inside; omega)

/-- The ordinary construction kernel executes all recursive requests and physical interning. -/
def intersect [DecidableEq Symbol] : Nat → (Value Symbol Unit × Value Symbol Unit) → Work Symbol Unit (Value Symbol Unit)
  | 0, _ => .pure .empty
  | fuel + 1, pair => node (intersect fuel) (nodeEdges pair.1) (nodeEdges pair.2)

/-- A zero bound excludes all accepted terms of the left operand. -/
theorem bounded_zero_rejects (value : Value Symbol Unit) (bounded : Bounded 0 value) (term : Term Symbol) :
    ¬ Accepts value term := by
  rw [accepts_iff, bounded]
  simp

/-- Each recursive child contract follows from the smaller bound. No intersection-language law is assumed. -/
theorem intersect_correct [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (bounded : Bounded fuel pair.1) (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    let result := run (intersect fuel pair) state
    Facts result.2 ∧ Available result.2 result.1 ∧ ChildExact pair result.1 := by
  induction fuel generalizing pair state with
  | zero =>
      refine ⟨facts, empty_available state, ?_⟩
      intro term
      constructor
      · intro impossible
        exact False.elim (empty_rejects term impossible)
      · intro accepted
        exact False.elim (bounded_zero_rejects pair.1 bounded term accepted.1)
  | succ fuel ih =>
      have checked : ∀ edges ∈ pairs (nodeEdges pair.1) (nodeEdges pair.2),
          ∀ request ∈ edges.1.children.zip edges.2.children, ∀ next, Facts next → Inputs next request →
          Facts (run (intersect fuel request) next).2 ∧
            Available (run (intersect fuel request) next).2 (run (intersect fuel request) next).1 ∧
            ChildExact request (run (intersect fuel request) next).1 := by
        intro edges member request child next nextFacts nextInputs
        have original := (pairs_member _ _ edges).mp member
        exact ih request (bounded edges.1 original.1 request.1 (List.of_mem_zip child).1) next nextFacts nextInputs
      have result := node_checked (intersect fuel) (nodeEdges pair.1) (nodeEdges pair.2) checked state facts
        (resident_edges state facts.linked pair.1 inputs.1.resident)
        (resident_edges state facts.linked pair.2 inputs.2.resident)
      refine ⟨result.1, result.2.1, ?_⟩
      intro term
      exact (result.2.2 term).trans (and_congr (accepts_iff pair.1 term).symm (accepts_iff pair.2 term).symm)

/-- Structural size closes both completion and common-language correctness for finite stored ordinary records. -/
theorem finite_exact [DecidableEq Symbol] (left right : Value Symbol Unit) (state : State Symbol Unit)
    (facts : Facts state) (leftAvailable : Available state left) (rightAvailable : Available state right) :
    let result := run (intersect (sizeOf left) (left, right)) state
    Facts result.2 ∧ Available result.2 result.1 ∧
      ∀ term, Accepts result.1 term ↔ Accepts left term ∧ Accepts right term :=
  intersect_correct (sizeOf left) (left, right) (bounded_size _ _ (Nat.le_refl _)) state facts
    ⟨leftAvailable, rightAvailable⟩

/-- Extra descent fuel cannot change the finite-term language of the actual returned record. -/
theorem fuel_language [DecidableEq Symbol] (left right : Value Symbol Unit) (state : State Symbol Unit)
    (facts : Facts state) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (first second : Nat) (firstBound : sizeOf left ≤ first) (secondBound : sizeOf left ≤ second) (term : Term Symbol) :
    Accepts (run (intersect first (left, right)) state).1 term ↔
      Accepts (run (intersect second (left, right)) state).1 term := by
  have firstExact := intersect_correct first (left, right) (bounded_size _ _ firstBound)
    state facts ⟨leftAvailable, rightAvailable⟩
  have secondExact := intersect_correct second (left, right) (bounded_size _ _ secondBound)
    state facts ⟨leftAvailable, rightAvailable⟩
  exact (firstExact.2.2 term).trans (secondExact.2.2 term).symm

end MicroCFTA.SourceInternedIntersectionRows
