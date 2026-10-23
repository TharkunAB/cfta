import MicroCFTA.SourceCurrentOriginalRowClusterScan

namespace MicroCFTA.SourceCurrentOriginalRowClusterExecution
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Control" => SourceCurrentOriginalRowClusterScan.Control
local notation "execute" => SourceCurrentOriginalRowClusterScan.execute
local notation "step" => SourceCurrentOriginalRowClusterScan.step
variable {width : Nat}


/-- Compose a yielded prefix with the remaining scan fuel. -/
theorem yielded_add
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (used rest : Nat) (control next : Control) (before middle : Wrapper width)
    (observed : execute used control before = .yielded next middle) :
    execute (used + rest) control before = execute rest next middle := by
  induction used generalizing control before with
  | zero =>
      have same : control = next ∧ before = middle := by
        simpa only [execute, SourceCurrentOriginalRowClusterScan.Outcome.yielded.injEq] using observed
      rcases same with ⟨rfl, rfl⟩
      simp only [Nat.zero_add]
  | succ used ih =>
      cases one : step control before <;>
        simp only [execute, one] at observed
      case yielded following after =>
        simpa only [Nat.succ_add, execute, one] using ih following after observed
      all_goals cases observed

/-- Additional fuel retains the exact completed rows and full state. -/
theorem done_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel extra : Nat) (control : Control) (before after : Wrapper width)
    (kept : List Edge) (observed : execute fuel control before = .done kept after) :
    execute (fuel + extra) control before = .done kept after := by
  induction fuel generalizing control before with
  | zero => cases observed
  | succ fuel ih =>
      cases one : step control before <;>
        simp only [execute, one] at observed
      case yielded following middle =>
        simpa only [Nat.succ_add, execute, one] using ih following middle observed
      all_goals simpa only [Nat.succ_add, execute, one] using observed

/-- Two completed scans from the same control and state return the same rows and state. -/
theorem completed_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (firstFuel secondFuel : Nat) (control : Control)
    (before firstAfter secondAfter : Wrapper width) (firstRows secondRows : List Edge)
    (first : execute firstFuel control before = .done firstRows firstAfter)
    (second : execute secondFuel control before = .done secondRows secondAfter) :
    firstRows = secondRows ∧ firstAfter = secondAfter := by
  have firstStable : execute (firstFuel + secondFuel) control before = .done firstRows firstAfter :=
    done_stable firstFuel secondFuel control before firstAfter firstRows first
  have secondStable : execute (secondFuel + firstFuel) control before = .done secondRows secondAfter :=
    done_stable secondFuel firstFuel control before secondAfter secondRows second
  rw [Nat.add_comm secondFuel firstFuel] at secondStable
  exact SourceCurrentOriginalRowClusterScan.Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentOriginalRowClusterExecution
