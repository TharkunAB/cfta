import MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability

/-!
# Successful bound stability for first-seeded checked queries

Larger stage bounds preserve a supplied literal success. No readiness,
range plan, semantic law, or completed graph is a premise. Successful
observations at different bounds identify the value and complete state.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededWorkerStability
open InternedConstructorTemplates SourceCurrentAllocatedSeededWorker
open SourceCurrentAllocatedSeededWorkerCompletion (bind_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Larger projection and read bounds retain the same complete checked operand return. -/
theorem operand_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h P H : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : operand p h path values before = .done result after) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    operand P H path values before = .done result after := by
  cases projected : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | done value heap =>
      simp only [operand, projected] at actual
      simp only [operand, SourceCurrentConjunctionRowsWorkerStability.forest_done_stable projected enoughP enoughH]
      exact actual
  | pending | unresolved | exhausted =>
      simp only [operand, projected] at actual
      cases actual

/-- Larger native bounds retain any successful literal execution without a physical plan. -/
theorem leaf_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {n N : Nat} {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : leaf n left right before = .done result after) (enough : n ≤ N) :
    leaf N left right before = .done result after := by
  cases executed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value state =>
      simp only [leaf, executed] at actual
      have stable := SourceEqualityNativeDemand.done_stable n (N - n) _ before state value executed
      rw [show n + (N - n) = N by omega] at stable
      simp only [leaf, stable]
      exact actual
  | yielded | failed | blocked | constraintError =>
      simp only [leaf, executed] at actual
      cases actual

/-- Larger bounds preserve each completed head, tail, and native request in order. -/
theorem fold_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n P H N : Nat} {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : fold p h n values seed paths before = .done result after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughN : n ≤ N) :
    fold P H N values seed paths before = .done result after := by
  induction paths generalizing before result after with
  | nil => exact operand_done_stable actual enoughP enoughH
  | cons path paths ih =>
      obtain ⟨head, middle, operandDone, later⟩ := (bind_done_iff _ _ result after).mp actual
      obtain ⟨tail, final, restDone, leafDone⟩ := (bind_done_iff _ _ result after).mp later
      simp only [fold, operand_done_stable operandDone enoughP enoughH, Outcome.bind, ih restDone]
      exact leaf_done_stable leafDone enoughN

/-- Larger stage bounds preserve the same first-seeded success and complete state. -/
theorem seeded_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n P H N : Nat} {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : seeded p h n values paths before = .done result after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughN : n ≤ N) :
    seeded P H N values paths before = .done result after := by
  cases paths with
  | nil => exact actual
  | cons seed rest => exact fold_done_stable actual enoughP enoughH enoughN

/-- Successful fold bounds identify the same result and every checked-state component. -/
theorem fold_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n P H N : Nat} {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after later : Checked width} {first second : Value Symbol Guard}
    (one : fold p h n values seed paths before = .done first after)
    (two : fold P H N values seed paths before = .done second later) : first = second ∧ after = later := by
  have firstStable := fold_done_stable one (Nat.le_max_left p P) (Nat.le_max_left h H) (Nat.le_max_left n N)
  have secondStable := fold_done_stable two (Nat.le_max_right p P) (Nat.le_max_right h H) (Nat.le_max_right n N)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Successful seeded bounds identify the same result and every checked-state component. -/
theorem seeded_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n P H N : Nat} {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after later : Checked width} {first second : Value Symbol Guard}
    (one : seeded p h n values paths before = .done first after)
    (two : seeded P H N values paths before = .done second later) : first = second ∧ after = later := by
  have firstStable := seeded_done_stable one (Nat.le_max_left p P) (Nat.le_max_left h H) (Nat.le_max_left n N)
  have secondStable := seeded_done_stable two (Nat.le_max_right p P) (Nat.le_max_right h H) (Nat.le_max_right n N)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentAllocatedSeededWorkerStability
