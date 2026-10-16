import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability

namespace MicroCFTA.CurrentLocalStabilityChecks
open InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker SourceCurrentAllocatedLocalWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

-- Increasing all nine bounds keeps every successful component, then agrees with any other successful observation.
example {g s r e p h m c n G S R E P H M C N budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values first second : List (Value Symbol Guard)}
    {before after later : Checked width} {fourth savedFourth currentFourth : Fourth} {memo saved current : Memo}
    (one : reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done first after savedFourth saved)
    (two : reduce G S R E P H M C N budget loaded inherited values before fourth memo = .done second later currentFourth current) :
    reduce (g + 1) (s + 1) (r + 1) (e + 1) (p + 1) (h + 1) (m + 1) (c + 1) (n + 1)
        budget loaded inherited values before fourth memo = .done first after savedFourth saved ∧
      first = second ∧ after.native = later.native ∧ after.operations = later.operations ∧
      savedFourth = currentFourth ∧ saved = current := by
  have larger := reduce_done_stable one (Nat.le_succ g) (Nat.le_succ s) (Nat.le_succ r)
    (Nat.le_succ e) (Nat.le_succ p) (Nat.le_succ h) (Nat.le_succ m) (Nat.le_succ c) (Nat.le_succ n)
  obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := reduce_done_unique larger two
  cases sameState
  exact ⟨larger, sameValues, rfl, rfl, sameFourth, sameMemo⟩

end MicroCFTA.CurrentLocalStabilityChecks
