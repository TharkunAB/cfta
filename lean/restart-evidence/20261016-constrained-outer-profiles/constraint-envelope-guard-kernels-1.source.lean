import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.GuardEnvelopeChecks
open EqualityNormalize SourceGuards
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope

/-- Top contributes no retained atom or staged conjunction overhead. -/
theorem top_merge [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) :
    stages (GuardConjunction.merge le (.top : Guard Formula) .top) = 0 := by rfl

/-- The zero-stage Top input does not add a raw atom beside Same. -/
theorem top_same [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (left right : Path) :
    stages (GuardConjunction.merge le .top (.same left right)) ≤ 2 := by
  exact merge_stages le .top (.same left right) 0 1 (by rfl) (by rfl)

/-- A residual guard does not extract a positive equality from its hidden Same node. -/
theorem residual_guard (left right : Path) :
    stages (.not (.same left right) : Guard Formula) = 1 ∧
    SamePaths 0 (.not (.same left right) : Guard Formula) ∧
    SourceCompactGuards.sourceEqualities
      (⟨some [], .not (.same left right)⟩ : SourceSymbolicIndex.Constraint Formula) = some [] := by
  refine ⟨rfl, ?_, rfl⟩
  intro first second member
  simp [GuardConjunction.atoms] at member

/-- Nested positive And syntax constructs the actual staged normalized output. -/
theorem nested_positive :
    let guard : Guard Unit := .and [.and [.same [1000000] [1000001]], .and [.same [1000000, 2] [1000002]]]
    ∃ output, SourceCompactGuards.positiveNormalized guard = some output ∧
      SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds
        (positiveBudget 2 6).1 (positiveBudget 2 6).2 output := by
  dsimp only
  let guard : Guard Unit := .and [.and [.same [1000000] [1000001]], .and [.same [1000000, 2] [1000002]]]
  obtain ⟨output, done, _active, _meaning⟩ := SourceCompactGuards.positiveNormalized_exact (Symbol := Unit) guard
    [[[1000000], [1000001]], [[1000000, 2], [1000002]]]
    (by simp [guard, SourceCompactGuards.positive, SourceCompactGuards.positiveList])
  refine ⟨output, done, positive_bounds guard 6 2 (by rfl) ?_ output done⟩
  intro left right member
  simpa [guard, GuardConjunction.atoms] using member

/-- Two actual conjunctions use the first returned operation state and its derived vector. -/
theorem serial_conjoin [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second third : SourceEqualityConjoinAllocation.Constraint Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : SourceEqualityConstraintAllocation.Ready before.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready before.constraints second.stored)
    (thirdReady : SourceEqualityConstraintAllocation.Ready before.constraints third.stored)
    (firstLimits secondLimits thirdLimits : Limits)
    (firstBounds : Bounds firstLimits (SourceEqualityConjoinAllocation.readback first))
    (secondBounds : Bounds secondLimits (SourceEqualityConjoinAllocation.readback second))
    (thirdBounds : Bounds thirdLimits (SourceEqualityConjoinAllocation.readback third)) :
    ∃ middle current result after,
      SourceEqualityConjoinAllocation.conjoin le first second before = (.ok middle, current) ∧
      SourceEqualityConjoinAllocation.conjoin le middle third current = (.ok result, after) ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintAllocation.Ready after.constraints result.stored ∧
      Bounds (conjoinLimits (conjoinLimits firstLimits secondLimits) thirdLimits)
        (SourceEqualityConjoinAllocation.readback result) := by
  obtain ⟨middle, current, firstDone, currentValid, middleReady, growth, _cached, _read, middleBounds, _effective⟩ :=
    conjoin_complete le first second before valid firstReady secondReady firstLimits secondLimits firstBounds secondBounds
  have thirdCurrent := thirdReady.grows growth.constraint_growth
  obtain ⟨result, after, lastDone, afterValid, resultReady, _growth, _cached, _read, finalBounds, _effective⟩ :=
    conjoin_complete le middle third current currentValid middleReady thirdCurrent
      (conjoinLimits firstLimits secondLimits) thirdLimits middleBounds thirdBounds
  exact ⟨middle, current, result, after, firstDone, lastDone, afterValid, resultReady, finalBounds⟩

/-- Initial vectors derive the parent path bound after the actual raw conjunction allocation. -/
theorem conjoin_precheck_paths [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (first second : SourceEqualityConjoinAllocation.Constraint Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : SourceEqualityConstraintAllocation.Ready before.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready before.constraints second.stored)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.constraints inherited)
    (firstLimits secondLimits : Limits)
    (firstBounds : Bounds firstLimits (SourceEqualityConjoinAllocation.readback first))
    (secondBounds : Bounds secondLimits (SourceEqualityConjoinAllocation.readback second)) :
    ∃ result after, SourceEqualityConjoinAllocation.conjoin le first second before = (.ok result, after) ∧
      ∀ records, (SourceEqualityPartialPrecheckAllocation.run result.stored result.guard inherited after).1 = .ok (.classes records) →
        ∀ record ∈ records, ∀ path ∈ record.paths,
          path.length ≤ (effectiveBudget (conjoinLimits firstLimits secondLimits)).2 := by
  obtain ⟨result, after, done, afterValid, ready, growth, cached, built, _bounds, bound⟩ :=
    conjoin_complete le first second before valid firstReady secondReady firstLimits secondLimits firstBounds secondBounds
  refine ⟨result, after, done, ?_⟩
  exact SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.allocated_precheck_paths result.stored result.guard inherited after
    afterValid ready (inheritedReady.grows growth.constraint_growth)
    (SourceEqualityConjoinAllocation.readback result).equalities cached built
    (effectiveBudget (conjoinLimits firstLimits secondLimits)).1 (effectiveBudget (conjoinLimits firstLimits secondLimits)).2 bound

end MicroCFTA.GuardEnvelopeChecks

#print axioms MicroCFTA.GuardEnvelopeChecks.top_merge
#check @MicroCFTA.GuardEnvelopeChecks.top_merge
#print axioms MicroCFTA.GuardEnvelopeChecks.top_same
#check @MicroCFTA.GuardEnvelopeChecks.top_same
#print axioms MicroCFTA.GuardEnvelopeChecks.residual_guard
#check @MicroCFTA.GuardEnvelopeChecks.residual_guard
#print axioms MicroCFTA.GuardEnvelopeChecks.nested_positive
#check @MicroCFTA.GuardEnvelopeChecks.nested_positive
#print axioms MicroCFTA.GuardEnvelopeChecks.serial_conjoin
#check @MicroCFTA.GuardEnvelopeChecks.serial_conjoin
#print axioms MicroCFTA.GuardEnvelopeChecks.conjoin_precheck_paths
#check @MicroCFTA.GuardEnvelopeChecks.conjoin_precheck_paths
