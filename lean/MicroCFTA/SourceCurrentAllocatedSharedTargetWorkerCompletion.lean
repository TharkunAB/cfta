import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion

/-!
# Stable execution of current shared targets and leaves

Finite force and leaf graphs derive sufficient bounds for their literal
workers. Larger bounds retain the same full checked state, slots, and merge
memo. The native request uses the exact checked state returned by forcing.
General outer completion and host demand remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion
open InternedConstructorTemplates SourceCurrentAllocatedSharedTargetState
open SourceCurrentAllocatedSharedTargetWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path

/-- Every larger pair of stage bounds retains the same complete shared return. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome width)
    (value : Value Symbol Guard) (after : State width) : Prop :=
  ∃ projection read merge selection native, ∀ p h m s n,
    projection ≤ p → read ≤ h → merge ≤ m → selection ≤ s → native ≤ n →
      evaluation p h m s n = .done value after

/-- The two completed stages combine their bounds at the exact intermediate state. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Outcome width)
    (next : Nat → Nat → Nat → Nat → Nat → Value Symbol Guard → State width → Outcome width)
    (value : Value Symbol Guard) (middle : State width) (result : Value Symbol Guard) (after : State width)
    (one : StableRun first value middle)
    (two : StableRun (fun p h m s n => next p h m s n value middle) result after) :
    StableRun (fun p h m s n => (first p h m s n).bind (next p h m s n)) result after := by
  obtain ⟨p, h, m, s, n, done⟩ := one
  obtain ⟨q, i, k, t, j, later⟩ := two
  refine ⟨max p q, max h i, max m k, max s t, max n j, ?_⟩
  intro a b c d e hp hh hm hs hn
  simp only [done a b c d e (Nat.le_trans (Nat.le_max_left _ _) hp)
    (Nat.le_trans (Nat.le_max_left _ _) hh) (Nat.le_trans (Nat.le_max_left _ _) hm)
    (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hn),
    Outcome.bind, later a b c d e (Nat.le_trans (Nat.le_max_right _ _) hp)
      (Nat.le_trans (Nat.le_max_right _ _) hh) (Nat.le_trans (Nat.le_max_right _ _) hm)
      (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_right _ _) hn)]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {record : Record} {values : List (Value Symbol Guard)} {path : Path}
variable {before after : State width} {value input : Value Symbol Guard}

/-- A finite force graph derives stable literal reuse or stable completed target construction. -/
theorem force_complete
    (actual : SourceCurrentAllocatedSharedTargetForce.Force record values path before value after) :
    StableRun (fun p h m s n => force p h m s n record values path before) value after := by
  cases actual with
  | hit present => exact ⟨0, 0, 0, 0, 0, by intros; simp only [force, present]⟩
  | miss absent target =>
      obtain ⟨p, h, m, s, n, stable⟩ := SourceCurrentAllocatedTargetWorkerCompletion.target_complete target
      refine ⟨p, h, m, s, n, ?_⟩
      intro a b c d e hp hh hm hs hn
      simp only [force, absent, stable a b c d e hp hh hm hs hn]

/-- The same checked request supplies a stable native bound without changing shared tables. -/
theorem step_complete {target : Value Symbol Guard} {checked : SourceEqualityNativeDemand.State width}
    (actual : SourceCurrentAllocatedTargetQuery.Step target input before.checked value checked) :
    StableRun (fun _ _ _ _ n => step n target input before) value (advance before checked) := by
  obtain ⟨bound, done⟩ := actual.done
  refine ⟨0, 0, 0, 0, bound, ?_⟩
  intro p h m s n _ _ _ _ enough
  have stable := SourceEqualityNativeDemand.done_stable bound (n - bound)
    (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input))
    before.checked checked value done
  rw [show bound + (n - bound) = n by omega] at stable
  simp only [step, stable]

/-- Completed leaves retain the exact force return before the stable checked intersection. -/
theorem leaf_complete
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record values path input before value after) :
    StableRun (fun p h m s n => leaf p h m s n record values path input before) value after := by
  cases actual with
  | apply forced query =>
      exact bind_stable _ _ _ _ _ _ (force_complete forced) (step_complete query)

end MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion
