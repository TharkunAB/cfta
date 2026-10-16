import MicroCFTA.SourceCurrentAllocatedClassWorker
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion

/-!
# Stable bounds for the current checked class pass

Each finite compiled class and right fold derives six sufficient bounds.
Larger bounds retain the same forest, checked state, and merge memo. The
literal shared edit worker supplies class execution. No completed callback
implements a branch, and no class resets the caller's warm operation tables.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
open InternedConstructorTemplates
open SourceCurrentAllocatedClassWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record

/-- All larger stage bounds retain the same complete returned class observation. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width)
    (values : List (Value Symbol Guard)) (after : Checked width) (saved : Memo) : Prop :=
  ∃ edit projection read merge selection native, ∀ e p h m s n,
    edit ≤ e → projection ≤ p → read ≤ h → merge ≤ m → selection ≤ s → native ≤ n →
      evaluation e p h m s n = .done values after saved

/-- Ordered completed stages combine their six bounds at the same returned checked state. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width)
    (next : Nat → Nat → Nat → Nat → Nat → Nat → List (Value Symbol Guard) → Checked width → Memo → Outcome width)
    (values : List (Value Symbol Guard)) (middle : Checked width) (current : Memo)
    (results : List (Value Symbol Guard)) (after : Checked width) (saved : Memo)
    (one : StableRun first values middle current)
    (two : StableRun (fun e p h m s n => next e p h m s n values middle current) results after saved) :
    StableRun (fun e p h m s n => (first e p h m s n).bind (next e p h m s n)) results after saved := by
  obtain ⟨e, p, h, m, s, n, done⟩ := one
  obtain ⟨E, P, H, M, S, N, later⟩ := two
  refine ⟨max e E, max p P, max h H, max m M, max s S, max n N, ?_⟩
  intro a b c d f g he hp hh hm hs hn
  simp only [done a b c d f g (Nat.le_trans (Nat.le_max_left _ _) he) (Nat.le_trans (Nat.le_max_left _ _) hp)
    (Nat.le_trans (Nat.le_max_left _ _) hh) (Nat.le_trans (Nat.le_max_left _ _) hm)
    (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hn), Outcome.bind,
    later a b c d f g (Nat.le_trans (Nat.le_max_right _ _) he) (Nat.le_trans (Nat.le_max_right _ _) hp)
      (Nat.le_trans (Nat.le_max_right _ _) hh) (Nat.le_trans (Nat.le_max_right _ _) hm)
      (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_right _ _) hn)]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A finite current class runs the actual compiled edit at its original full state. -/
theorem class_complete {record : Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassEdits.Class record values before memo results after saved) :
    StableRun (fun e p h m s n => runClass e p h m s n record values before memo) results after saved := by
  cases actual with
  | edit lower =>
      obtain ⟨e, p, h, m, s, n, stable⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.list_complete lower
      refine ⟨e, p, h, m, s, n, ?_⟩
      intro a b c d f g he hp hh hm hs hn
      simp only [runClass, stable a b c d f g he hp hh hm hs hn]

/-- The same actual right fold supplies all six shared execution bounds. -/
theorem fold_complete {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassPass.Fold records values before memo results after saved) :
    StableRun (fun e p h m s n => fold e p h m s n records values before memo) results after saved := by
  induction actual with
  | nil => exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  | cons tail head ih => exact bind_stable _ _ _ _ _ _ _ _ ih (class_complete head)

/-- Final propagation retains the stable checked state and memo of the full fold. -/
theorem pass_complete {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassPass.Pass records values before memo results after saved) :
    StableRun (fun e p h m s n => pass e p h m s n records values before memo) results after saved := by
  cases actual with
  | done lower =>
      obtain ⟨e, p, h, m, s, n, stable⟩ := fold_complete lower
      refine ⟨e, p, h, m, s, n, ?_⟩
      intro a b c d f g he hp hh hm hs hn
      simp only [pass, stable a b c d f g he hp hh hm hs hn, Outcome.bind]

end MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
