import MicroCFTA.SourceInternedIntersectionDispatch

/-!
# Derived language of ordinary dispatch and its recursive child calls

The proofs use actual available operands at each cache state. Closed self
calls read an existing canonical record. Ordered calls may allocate in a
different order, but their finite-term language is the same conjunction.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency MergedPhysicalGroupCalls Language
open SourceInternedIntersectionRows

/-- Ordering keeps both concrete operands available. -/
theorem ordered_inputs (state : State Symbol Unit) (pair : Value Symbol Unit × Value Symbol Unit)
    (inputs : Inputs state pair) : Inputs state (ordered pair) := by
  unfold ordered
  split
  · exact ⟨inputs.2, inputs.1⟩
  · exact inputs

/-- Ordering keeps a common recursive bound on both operands. -/
theorem ordered_bounds (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (left : Bounded fuel pair.1) (right : Bounded fuel pair.2) :
    Bounded fuel (ordered pair).1 ∧ Bounded fuel (ordered pair).2 := by
  unfold ordered
  split
  · exact ⟨right, left⟩
  · exact ⟨left, right⟩

/-- Ordering retains the finite plain record restriction. -/
theorem ordered_plain (pair : Value Symbol Unit × Value Symbol Unit) (left : Plain pair.1) (right : Plain pair.2) :
    Plain (ordered pair).1 ∧ Plain (ordered pair).2 := by
  unfold ordered
  split
  · exact ⟨right, left⟩
  · exact ⟨left, right⟩

/-- Ordering does not change which finite terms belong to both operands. -/
theorem ordered_language (pair : Value Symbol Unit × Value Symbol Unit) (term : Term Symbol) :
    (Accepts (ordered pair).1 term ∧ Accepts (ordered pair).2 term) ↔
      Accepts pair.1 term ∧ Accepts pair.2 term := by
  unfold ordered
  split
  · exact and_comm
  · exact Iff.rfl

/-- An empty operand excludes every common finite term. -/
theorem empty_common (pair : Value Symbol Unit × Value Symbol Unit) (empty : hasEmpty pair = true)
    (term : Term Symbol) : ¬ (Accepts pair.1 term ∧ Accepts pair.2 term) := by
  simp only [hasEmpty, Bool.or_eq_true, beq_iff_eq] at empty
  intro accepted
  rcases empty with first | second
  · have same := (EqualityLeafProjectionPhysical.reference_empty pair.1).mp first
    exact empty_rejects term (same ▸ accepted.1)
  · have same := (EqualityLeafProjectionPhysical.reference_empty pair.2).mp second
    exact empty_rejects term (same ▸ accepted.2)

/-- Plain recursive child results make the actual normalized parent plain. -/
theorem node_plain_checked [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit))
    (checked : ∀ pair ∈ pairs left right, ∀ request ∈ pair.1.children.zip pair.2.children,
      ∀ state, Facts state → Inputs state request →
        Facts (run (call request) state).2 ∧ Available (run (call request) state).2 (run (call request) state).1 ∧
          Plain (run (call request) state).1)
    (state : State Symbol Unit) (facts : Facts state) (leftResident : Edges state left) (rightResident : Edges state right) :
    Plain (run (node call left right) state).1 := by
  let relation := fun (_ : EdgeValue Symbol Unit × EdgeValue Symbol Unit) (edge : EdgeValue Symbol Unit) =>
    ∀ child ∈ edge.children, Plain child
  have edgeChecked : ∀ pair ∈ pairs left right, ∀ next, Facts next → EdgeInputs next pair →
      Facts (run (edge call pair) next).2 ∧ EdgeResident (run (edge call pair) next).2 (run (edge call pair) next).1 ∧
        relation pair (run (edge call pair) next).1 := by
    intro pair member next nextFacts nextInputs
    have built := edge_checked call pair (fun _ value => Plain value) (checked pair member) next nextFacts nextInputs
    refine ⟨built.1, built.2.1, ?_⟩
    have children := built.2.2.2.2
    split at children
    · exact all₂_plain _ _ children
    · intro child member
      rw [children] at member
      rw [List.mem_singleton.mp member]
      exact .empty
  have inputs : ∀ pair ∈ pairs left right, EdgeInputs state pair := by
    intro pair member
    have original := (pairs_member _ _ pair).mp member
    exact ⟨leftResident _ original.1, rightResident _ original.2.1⟩
  have built := map_checked (edge call) _ EdgeInputs EdgeResident relation
    edgeInputs_stable resident_stable edgeChecked state facts inputs
  simp only [node, run_bind]
  apply makeNode_plain _ _ built.1 built.2.1
  have property : ∀ (requests : List (EdgeValue Symbol Unit × EdgeValue Symbol Unit)) (edges : List (EdgeValue Symbol Unit)),
      All₂ relation requests edges → ∀ edge ∈ edges, ∀ child ∈ edge.children, Plain child := by
    intro requests edges related
    induction related with
    | nil => simp
    | cons head tail ih =>
        intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact ih edge member
  exact property _ _ built.2.2

/-- Actual empty, self, ordered, and recursive ordinary execution has the common language. -/
theorem dispatch_correct [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (leftBound : Bounded fuel pair.1) (rightBound : Bounded fuel pair.2)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    let result := run (dispatch fuel pair) state
    Facts result.2 ∧ Available result.2 result.1 ∧ Plain result.1 ∧ ChildExact pair result.1 := by
  induction fuel generalizing pair state with
  | zero =>
      refine ⟨facts, empty_available state, .empty, ?_⟩
      intro term
      exact ⟨fun accepted => False.elim (empty_rejects term accepted),
        fun accepted => False.elim (bounded_zero_rejects pair.1 leftBound term accepted.1)⟩
  | succ fuel ih =>
      by_cases empty : hasEmpty pair = true
      · simp only [dispatch, empty, ↓reduceIte, run]
        refine ⟨facts, empty_available state, .empty, ?_⟩
        intro term
        exact ⟨fun accepted => False.elim (empty_rejects term accepted),
          fun accepted => False.elim (empty_common pair empty term accepted)⟩
      · by_cases same : closedSelf pair = true
        · simp only [dispatch, empty, same, ↓reduceIte]
          refine ⟨facts, inputs.1, leftPlain, ?_⟩
          intro term
          rw [← self_record state facts pair inputs same]
          exact ⟨fun accepted => ⟨accepted, accepted⟩, And.left⟩
        · have orderedInputs := ordered_inputs state pair inputs
          have orderedBounds := ordered_bounds (fuel + 1) pair leftBound rightBound
          have orderedPlain := ordered_plain pair leftPlain rightPlain
          have calls : ∀ edges ∈ pairs (nodeEdges (ordered pair).1) (nodeEdges (ordered pair).2),
              ∀ request ∈ edges.1.children.zip edges.2.children, ∀ next, Facts next → Inputs next request →
              Facts (run (dispatch fuel request) next).2 ∧ Available (run (dispatch fuel request) next).2
                (run (dispatch fuel request) next).1 ∧ Plain (run (dispatch fuel request) next).1 ∧
                ChildExact request (run (dispatch fuel request) next).1 := by
            intro edges member request included next nextFacts nextInputs
            have original := (pairs_member _ _ edges).mp member
            have children := List.of_mem_zip included
            exact ih request (orderedBounds.1 edges.1 original.1 request.1 children.1)
              (orderedBounds.2 edges.2 original.2.1 request.2 children.2)
              (orderedPlain.1.children _ edges.1 original.1 request.1 children.1)
              (orderedPlain.2.children _ edges.2 original.2.1 request.2 children.2) next nextFacts nextInputs
          have leftRows := resident_edges state facts.linked (ordered pair).1 orderedInputs.1.resident
          have rightRows := resident_edges state facts.linked (ordered pair).2 orderedInputs.2.resident
          have result := node_checked (dispatch fuel) _ _
            (fun edges member request included next nextFacts nextInputs =>
              let child := calls edges member request included next nextFacts nextInputs
              ⟨child.1, child.2.1, child.2.2.2⟩) state facts leftRows rightRows
          have plain := node_plain_checked (dispatch fuel) _ _
            (fun edges member request included next nextFacts nextInputs =>
              let child := calls edges member request included next nextFacts nextInputs
              ⟨child.1, child.2.1, child.2.2.1⟩) state facts leftRows rightRows
          simp only [dispatch, empty, same]
          refine ⟨result.1, result.2.1, plain, ?_⟩
          intro term
          exact (result.2.2 term).trans ((and_congr (accepts_iff _ term).symm (accepts_iff _ term).symm).trans
            (ordered_language pair term))

/-- A bound derived from both physical records suffices even when their order changes. -/
noncomputable def bound (pair : Value Symbol Unit × Value Symbol Unit) := max (sizeOf pair.1) (sizeOf pair.2)

/-- Each completed native ordinary callback derives its own common-language result. -/
theorem finite_exact [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    let result := run (dispatch (bound pair) pair) state
    Facts result.2 ∧ Available result.2 result.1 ∧ Plain result.1 ∧ ChildExact pair result.1 :=
  dispatch_correct (bound pair) pair (bounded_size _ _ (Nat.le_max_left _ _))
    (bounded_size _ _ (Nat.le_max_right _ _)) leftPlain rightPlain state facts inputs

end MicroCFTA.SourceInternedIntersectionDispatch
