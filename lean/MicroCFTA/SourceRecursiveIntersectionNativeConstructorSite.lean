import MicroCFTA.SourceRecursiveIntersectionNativePrefixCoverage

/-!
# Exact source site of an actual pending constructor

A pending native constructor can arise only at an optional-binder
instruction. An actual bounded blocked run derives its finite yielded
prefix, original source body, pre-call native state, and exact returned
heap. No source-site witness is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- One actual constructor block identifies its original optional-binder instruction and exact source effect. -/
theorem step_constructor_site [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code remaining : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (blocked : step emptyGuard conjoin code state = .blocked (.constructor key) remaining after) :
    ∃ pair body next heap, code = .optionalBinder pair body next ∧ remaining = .optionalBinder pair body next ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap = .pending key heap ∧
      after = advance state {state.machine with heap := heap} := by
  cases code with
  | pure | fail | work | enter | read | finishNode | finishEdge => cases blocked
  | optionalBinder pair body next =>
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap with
      | done => simp only [step, constructed] at blocked; cases blocked
      | pending actual heap =>
          have same := Outcome.blocked.inj (by simpa only [step, constructed] using blocked)
          have equal := Blocked.constructor.inj same.1
          subst actual
          exact ⟨pair, body, next, heap, rfl, same.2.1.symm, constructed, same.2.2.symm⟩
  | node request next =>
      cases lookup : lookupNode width request state with
      | mk selection chosen =>
        cases selection with
        | direct => simp only [step, lookup] at blocked; cases blocked
        | memoized handle =>
          cases demand : demandNode handle chosen with
          | mk observation current => cases observation <;> simp only [step, lookup, demand] at blocked <;> cases blocked
  | edge request next =>
      cases lookup : lookupEdge width request state with
      | mk handle chosen =>
        cases demand : demandEdge handle chosen with
        | mk observation current => cases observation <;> simp only [step, lookup, demand] at blocked <;> cases blocked

/-- An actual finite constructor block derives its exact earlier source site and complete yielded prefix. -/
theorem constructor_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (code remaining : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (blocked : execute emptyGuard conjoin fuel code state = .blocked (.constructor key) remaining after) :
    ∃ steps before pair body next heap, steps < fuel ∧
      Steps emptyGuard conjoin steps code state (.optionalBinder pair body next) before ∧
      remaining = .optionalBinder pair body next ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.machine.heap = .pending key heap ∧
      after = advance before {before.machine with heap := heap} := by
  induction fuel generalizing code state with
  | zero => cases blocked
  | succ fuel ih =>
      cases one : step emptyGuard conjoin code state with
      | done | failed => simp only [execute, one] at blocked; cases blocked
      | yielded rest current =>
          have tail : execute emptyGuard conjoin fuel rest current = .blocked (.constructor key) remaining after := by
            simpa only [execute, one] using blocked
          obtain ⟨steps, before, pair, body, next, heap, smaller, trace, original, constructed, final⟩ := ih rest current tail
          exact ⟨steps + 1, before, pair, body, next, heap, by omega,
            .cons _ _ _ _ _ _ steps one trace, original, constructed, final⟩
      | blocked reason rest current =>
          have same := Outcome.blocked.inj (by simpa only [execute, one] using blocked)
          rcases same with ⟨rfl, rfl, rfl⟩
          obtain ⟨pair, body, next, heap, head, original, constructed, final⟩ :=
            step_constructor_site emptyGuard conjoin code _ state _ key one
          exact ⟨0, state, pair, body, next, heap, by omega, by rw [← head]; exact .refl _ _, original, constructed, final⟩

end MicroCFTA.SourceRecursiveIntersectionNative
