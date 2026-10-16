import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope

namespace MicroCFTA.ConstraintEnvelopeChecks
open EqualityNormalize SourceEqualityClassOrder
open SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope

private def initial : Constraints := [[[0], [1, 1]], [[0, 2], [3]]]
private def extended : Constraints := [[[0], [1, 1]], [[0, 2], [1, 1, 2], [3]]]

/-- A literal source step creates a path longer than every original path. -/
theorem suffix_extension :
    Bounds 4 2 initial ∧ congruenceStep initial = some extended ∧
    [1, 1, 2] ∈ extended.flatten ∧ ¬ ([1, 1, 2] : Path).length ≤ 2 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  constructor
  · decide
  · simp [initial]

/-- The actual fixed-point algorithm retains the longer generated path. -/
theorem completed_extension : mkEqConstraints 3 initial = .normalized extended := by decide

/-- Large natural indices require no numerical range or arity premise. -/
theorem unbounded_indices : Envelope 2 2 (SourceCompactGuards.normalize [[[1000000], [1000001, 1000002]]]) := by
  apply normalize
  constructor
  · decide
  · simp

/-- Combination constructs its physical result before descent derives the shorter envelope. -/
theorem combine_then_descend (inherited own : SourceEqualityPrecheck.Constraint)
    (firstCount secondCount firstDepth secondDepth index : Nat)
    (first : PayloadBounds firstCount firstDepth inherited)
    (second : PayloadBounds secondCount secondDepth own) :
    ∃ combined, SourceEqualityInheritedPayload.combine inherited own = .ok combined ∧
      PayloadBounds
        ((firstCount + secondCount) * wordCount ((firstCount + secondCount) * max firstDepth secondDepth)
          (normalizedDepth (firstCount + secondCount) (max firstDepth secondDepth)))
        (normalizedDepth (firstCount + secondCount) (max firstDepth secondDepth) - 1)
        (SourceEqualityDescend.descend combined index) := by
  obtain ⟨combined, done, valid, _meaning⟩ :=
    SourceEqualityInheritedPayload.combine_complete (Symbol := Unit) inherited own
  exact ⟨combined, done, payload_descend combined index _ _ valid
    (payload_combine inherited own combined first second done).bounds⟩

/-- Every live precheck keeps the original own occurrence and depth bounds. -/
theorem live_original_only (own inherited : SourceEqualityPrecheck.Constraint)
    (occurrences depth : Nat) (input : PayloadBounds occurrences depth own) :
    ∀ records, SourceEqualityPrecheck.precheck own inherited = .ok (.classes records) →
      (records.map Record.paths).flatten.length ≤ occurrences ∧
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
  intro records done
  exact ⟨(precheck_bounds own inherited occurrences depth input records done).occurrences,
    precheck_paths own inherited occurrences depth input records done⟩

/-- Initial physical readiness gives the parent path obligation at every actual classes branch. -/
theorem initial_allocated_paths
    (stored : SourceEqualityConstraintAllocation.Value) (guard : SourceGuards.Guard Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.constraints inherited)
    (original : Option Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload) (occurrences depth : Nat)
    (input : OptionBounds occurrences depth
      (SourceCompactGuards.sourceEqualities (⟨original, guard⟩ : SourceSymbolicIndex.Constraint Formula))) :
    ∀ records, (SourceEqualityPartialPrecheckAllocation.run stored guard inherited before).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth :=
  allocated_precheck_paths stored guard inherited before valid storedReady inheritedReady original cached built occurrences depth input

/-- Empty and contradiction payloads preserve their literal indexed-descent cases. -/
theorem terminal_descent (index : Nat) :
    SourceEqualityDescend.descend none index = none ∧
    SourceEqualityDescend.descend (some []) index = some [] ∧
    PayloadBounds 0 0 (SourceEqualityDescend.descend (some []) index) := by
  refine ⟨rfl, rfl, ?_⟩
  intro output done
  have same : ([] : Constraints) = output := Option.some.inj done
  subst output
  constructor <;> simp

end MicroCFTA.ConstraintEnvelopeChecks

#print axioms MicroCFTA.ConstraintEnvelopeChecks.suffix_extension
#check @MicroCFTA.ConstraintEnvelopeChecks.suffix_extension
#print axioms MicroCFTA.ConstraintEnvelopeChecks.completed_extension
#check @MicroCFTA.ConstraintEnvelopeChecks.completed_extension
#print axioms MicroCFTA.ConstraintEnvelopeChecks.unbounded_indices
#check @MicroCFTA.ConstraintEnvelopeChecks.unbounded_indices
#print axioms MicroCFTA.ConstraintEnvelopeChecks.combine_then_descend
#check @MicroCFTA.ConstraintEnvelopeChecks.combine_then_descend
#print axioms MicroCFTA.ConstraintEnvelopeChecks.live_original_only
#check @MicroCFTA.ConstraintEnvelopeChecks.live_original_only
#print axioms MicroCFTA.ConstraintEnvelopeChecks.initial_allocated_paths
#check @MicroCFTA.ConstraintEnvelopeChecks.initial_allocated_paths
#print axioms MicroCFTA.ConstraintEnvelopeChecks.terminal_descent
#check @MicroCFTA.ConstraintEnvelopeChecks.terminal_descent
