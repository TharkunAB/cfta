import MicroCFTA.SourceCurrentAllocatedSeededWorker
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Stable finite bounds for actual first-seeded graphs

Every completed projection and checked native trace supplies a finite bound.
The ordered fold combines these bounds at each actual intermediate state.
No recursive completion callback or future state law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
open InternedConstructorTemplates SourceCurrentAllocatedSeededWorker
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- All larger projection, read, and native bounds retain the exact checked return. -/
def StableRun (evaluation : Nat → Nat → Nat → Outcome width)
    (result : Value Symbol Guard) (after : Checked width) : Prop :=
  ∃ p h n, ∀ P H N, p ≤ P → h ≤ H → n ≤ N → evaluation P H N = .done result after

/-- A completed bind exposes the complete actual intermediate state. -/
theorem bind_done_iff (first : Outcome width)
    (next : Value Symbol Guard → Checked width → Outcome width)
    (result : Value Symbol Guard) (after : Checked width) :
    first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro actual; exact ⟨value, state, rfl, actual⟩
      · rintro ⟨_, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

/-- Stable prefixes compose at their literal returned checked state. -/
theorem bind_stable (first : Nat → Nat → Nat → Outcome width)
    (next : Nat → Nat → Nat → Value Symbol Guard → Checked width → Outcome width)
    (value : Value Symbol Guard) (middle : Checked width) (result : Value Symbol Guard) (after : Checked width)
    (one : StableRun first value middle)
    (two : StableRun (fun p h n => next p h n value middle) result after) :
    StableRun (fun p h n => (first p h n).bind (next p h n)) result after := by
  obtain ⟨p, h, n, done⟩ := one
  obtain ⟨laterP, laterH, laterN, nextDone⟩ := two
  refine ⟨max p laterP, max h laterH, max n laterN, ?_⟩
  intro P H N enoughP enoughH enoughN
  simp only [done P H N (Nat.le_trans (Nat.le_max_left _ _) enoughP)
    (Nat.le_trans (Nat.le_max_left _ _) enoughH) (Nat.le_trans (Nat.le_max_left _ _) enoughN), Outcome.bind,
    nextDone P H N (Nat.le_trans (Nat.le_max_right _ _) enoughP)
      (Nat.le_trans (Nat.le_max_right _ _) enoughH) (Nat.le_trans (Nat.le_max_right _ _) enoughN)]

/-- Actual forest execution supplies projection and stored-read bounds. -/
theorem operand_complete [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Operand path values before result after) :
    StableRun (fun p h _ => operand p h path values before) result after := by
  cases actual with
  | force heap projected =>
      obtain ⟨p, h, stable⟩ := SourceEqualityProjectionWorkerComplete.forest_stable projected
      exact ⟨p, h, 0, by
        intro P H N enoughP enoughH _
        simp only [operand, stable P H enoughP enoughH]⟩

/-- An actual checked trace supplies native bounds at its exact returned state. -/
theorem leaf_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      before (.code (.pure result)) after) :
    StableRun (fun _ _ n => leaf n left right before) result after := by
  have done := SourceEqualityNativeDemand.trace_done fuel _ before after result actual.steps
  refine ⟨0, 0, fuel + 1, ?_⟩
  intro P H N _ _ enough
  have stable := SourceEqualityNativeDemand.done_stable (fuel + 1) (N - (fuel + 1)) _ before after result done
  rw [show fuel + 1 + (N - (fuel + 1)) = N by omega] at stable
  simp only [leaf, stable]

/-- The actual rotated fold supplies bounds for every ordered projection and native request. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Fold values (paths ++ [seed]) before result after) :
    StableRun (fun p h n => fold p h n values seed paths before) result after := by
  induction paths generalizing before result after with
  | nil =>
      cases actual with
      | one first => exact operand_complete first
  | cons path paths ih =>
      have nonempty : paths ++ [seed] ≠ [] := by simp
      cases tailShape : paths ++ [seed] with
      | nil => exact (nonempty tailShape).elim
      | cons next rest =>
          have shaped : Fold values (path :: next :: rest) before result after := by
            simpa only [List.cons_append, tailShape] using actual
          cases shaped with
          | cons first remaining native =>
              have tail := remaining
              rw [← tailShape] at tail
              exact bind_stable _ _ _ _ _ _ (operand_complete first)
                (bind_stable _ _ _ _ _ _ (ih tail) (leaf_complete native))

/-- Every actual seeded graph has stable execution at its full returned checked state. -/
theorem seeded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Seeded values paths before result after) :
    StableRun (fun p h n => seeded p h n values paths before) result after := by
  cases actual with
  | nil => exact ⟨0, 0, 0, by intros; rfl⟩
  | nonempty actual => exact fold_complete actual

/-- A single bound can supply the three independently constructed stage bounds. -/
theorem seeded_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Seeded values paths before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → seeded fuel fuel fuel values paths before = .done result after := by
  obtain ⟨p, h, n, stable⟩ := seeded_complete actual
  refine ⟨max (max p h) n, ?_⟩
  intro fuel enough
  exact stable fuel fuel fuel (by omega) (by omega) (by omega)

end MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
