import MicroCFTA.SourceInternedIntersectionDispatchExact

/-!
# Completion and administrative guards of ordinary native dispatch

The source first handles EmptyNode, then resets a closed call's nonempty
free environment, then tests closed self equality and operand order. On a
public empty domain no repeated-pair branch is possible. Sufficient descent
fuel fixes the complete physical computation, including final cache state.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency MergedPhysicalGroupCalls Language
open SourceInternedIntersectionRows

/-- Every complete immutable record has positive structural size. -/
theorem record_positive (value : Value Symbol Unit) : 0 < sizeOf value := by
  cases value <;> simp [Value.empty.sizeOf_spec, Value.reference.sizeOf_spec, Value.node.sizeOf_spec,
    Value.union.sizeOf_spec, Value.mu.sizeOf_spec] <;> omega

/-- A common structural bound survives operand ordering. -/
theorem ordered_sizes (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (left : sizeOf pair.1 ≤ fuel) (right : sizeOf pair.2 ≤ fuel) :
    sizeOf (ordered pair).1 ≤ fuel ∧ sizeOf (ordered pair).2 ≤ fuel := by
  unfold ordered
  split
  · exact ⟨right, left⟩
  · exact ⟨left, right⟩

/-- Extra descent fuel preserves the entire concrete dispatched computation. -/
theorem dispatch_stable [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (left : sizeOf pair.1 ≤ fuel) (right : sizeOf pair.2 ≤ fuel) (extra : Nat) :
    dispatch (fuel + extra) pair = dispatch fuel pair := by
  induction fuel generalizing pair extra with
  | zero => have positive := record_positive pair.1; omega
  | succ fuel ih =>
      rw [Nat.succ_add]
      simp only [dispatch]
      split
      · rfl
      · split
        · rfl
        · apply node_congr
          intro edgePair member request inside
          have original := (pairs_member _ _ edgePair).mp member
          have children := List.of_mem_zip inside
          have sizes := ordered_sizes (fuel + 1) pair left right
          have leftLess := child_smaller (ordered pair).1 edgePair.1 original.1 request.1 children.1
          have rightLess := child_smaller (ordered pair).2 edgePair.2 original.2.1 request.2 children.2
          exact ih request (by omega) (by omega) extra

/-- The derived bound stabilizes both the returned physical record and the constructor cache. -/
theorem run_complete [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit) (state : State Symbol Unit) (extra : Nat) :
    run (dispatch (bound pair + extra) pair) state = run (dispatch (bound pair) pair) state := by
  rw [dispatch_stable (bound pair) pair (Nat.le_max_left _ _) (Nat.le_max_right _ _) extra]

/-- A public ordinary call has no recursive-pair domain entries. -/
def emptyDomain : IntersectionFlatMemoKeyDomain.DomainKey := ⟨[], []⟩

/-- Derived closed metadata reduces public source guards to the implemented branches. -/
theorem public_decision (pair : Value Symbol Unit × Value Symbol Unit) (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    decision emptyDomain pair =
      if hasEmpty pair then .empty else if closedSelf pair then .self
      else if greater pair.1 pair.2 then .swap else .ordinary := by
  have leftClosed := plain_closed pair.1 leftPlain state facts inputs.1
  have rightClosed := plain_closed pair.2 rightPlain state facts inputs.2
  simp [decision, emptyDomain, leftClosed, rightClosed]

/-- A nonempty free environment redirects a closed nonempty call before self and sorting. -/
theorem reset_decision (domain : IntersectionFlatMemoKeyDomain.DomainKey) (nonemptyDomain : domain.free ≠ [])
    (pair : Value Symbol Unit × Value Symbol Unit) (nonempty : hasEmpty pair = false)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    decision domain pair = .reset := by
  have leftClosed := plain_closed pair.1 leftPlain state facts inputs.1
  have rightClosed := plain_closed pair.2 rightPlain state facts inputs.2
  simp [decision, nonempty, leftClosed, rightClosed, nonemptyDomain]

/-- After source operand sorting, the next public call reaches the ordinary branch. -/
theorem swapped_decision (pair : Value Symbol Unit × Value Symbol Unit)
    (nonempty : hasEmpty pair = false) (different : closedSelf pair = false) (swap : greater pair.1 pair.2 = true)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    decision emptyDomain (pair.2, pair.1) = .ordinary := by
  have leftClosed := plain_closed pair.1 leftPlain state facts inputs.1
  have rightClosed := plain_closed pair.2 rightPlain state facts inputs.2
  have emptySwap : hasEmpty (pair.2, pair.1) = false := by simpa only [hasEmpty, Bool.or_comm] using nonempty
  have differentSwap : closedSelf (pair.2, pair.1) = false := by
    simp only [closedSelf, leftClosed, List.isEmpty_nil, Bool.and_true] at different
    simp only [closedSelf, rightClosed, List.isEmpty_nil, Bool.and_true]
    simpa only [beq_eq_false_iff_ne, ne_comm] using different
  rw [public_decision (pair.2, pair.1) rightPlain leftPlain state facts ⟨inputs.2, inputs.1⟩]
  simp [emptySwap, differentSwap, greater_swap pair.1 pair.2 swap]

/-- Completed dispatched ordinary calls have exact physical common language and stable effects. -/
theorem completed_physical_exact [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    ∃ result,
      (∀ extra, run (dispatch (bound pair + extra) pair) state = result) ∧
      Facts result.2 ∧ Available result.2 result.1 ∧ Plain result.1 ∧
      ∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph result.2 (fun _ _ => true)) result.1 term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) pair.1 term ∧
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) pair.2 term := by
  have result := finite_exact pair leftPlain rightPlain state facts inputs
  refine ⟨run (dispatch (bound pair) pair) state, run_complete pair state, result.1, result.2.1, result.2.2.1, ?_⟩
  intro term
  rw [plain_exact _ _ result.2.2.1, plain_exact state pair.1 leftPlain, plain_exact state pair.2 rightPlain]
  exact result.2.2.2 term

/-- The source shortcuts preserve the language of the previously checked ordinary construction kernel. -/
theorem kernel_language [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) (term : Term Symbol) :
    Accepts (run (dispatch (bound pair) pair) state).1 term ↔
      Accepts (run (SourceInternedIntersectionRows.intersect (sizeOf pair.1) pair) state).1 term := by
  exact ((finite_exact pair leftPlain rightPlain state facts inputs).2.2.2 term).trans
    ((SourceInternedIntersectionRows.finite_exact pair.1 pair.2 state facts inputs.1 inputs.2).2.2 term).symm

end MicroCFTA.SourceInternedIntersectionDispatch
