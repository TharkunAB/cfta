import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability

/-!
# Successful parent-edge execution under larger bounds

Raw rejection and field observations do not depend on stage bounds.
The live branch retains its exact successful local return before the same
checked constructor. All nine bounds can increase at a fixed budget.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentWorkerStability
open Language InternedConstructorTemplates
open SourceCurrentAllocatedParentWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Larger stage bounds preserve the exact lifted local forest and every returned table. -/
theorem local_done_stable {g s r e p h m c n G S R E P H M C N budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : reduceChildren g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after savedFourth saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    reduceChildren G S R E P H M C N budget loaded inherited values before fourth memo =
      .done results after savedFourth saved := by
  cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
      loaded inherited values before fourth memo with
  | done results checked current warm =>
      have stable := SourceCurrentAllocatedLocalWorkerStability.reduce_done_stable observed
        enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simp only [reduceChildren, observed] at actual
      simpa only [reduceChildren, stable] using actual
  | failed =>
      simp only [reduceChildren, observed] at actual
      cases actual

/-- Larger stage bounds preserve the same edge, complete checked state, fourth memo, and merge memo. -/
theorem edge_done_stable {g s r e p h m c n G S R E P H M C N budget : Nat}
    {symbol : Symbol} {original : Guard} {inherited : EqValue} {values : List (Value Symbol Guard)}
    {result : EdgeValue Symbol Guard} {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : edge g s r e p h m c n budget symbol original inherited values before fourth memo =
      .done result after savedFourth saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    edge G S R E P H M C N budget symbol original inherited values before fourth memo =
      .done result after savedFourth saved := by
  cases test : SourceEqualityMkEdgeAllocation.contradictory original with
  | true => simpa only [edge, test, ite_true] using actual
  | false =>
      cases found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints with
      | error =>
          simp only [edge, test, Bool.false_eq_true, ite_false, found] at actual
          cases actual
      | ok field =>
          cases field with
          | none =>
              simp only [edge, test, Bool.false_eq_true, ite_false, found] at actual
              cases actual
          | some loaded =>
              simp only [edge, test, Bool.false_eq_true, ite_false, found] at actual ⊢
              cases observed : reduceChildren g s r e p h m c n budget loaded inherited values before fourth memo with
              | done children checked current warm =>
                  have stable := local_done_stable observed enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
                  simp only [observed, Outcome.bind] at actual
                  simpa only [stable, Outcome.bind] using actual
              | failed =>
                  simp only [observed, Outcome.bind] at actual
                  cases actual

/-- Any two successful parent bounds identify the edge and all four returned components. -/
theorem edge_done_unique {g s r e p h m c n G S R E P H M C N budget : Nat}
    {symbol : Symbol} {original : Guard} {inherited : EqValue} {values : List (Value Symbol Guard)}
    {first second : EdgeValue Symbol Guard} {before after later : Checked width}
    {fourth savedFourth currentFourth : Fourth} {memo saved current : Memo}
    (one : edge g s r e p h m c n budget symbol original inherited values before fourth memo =
      .done first after savedFourth saved)
    (two : edge G S R E P H M C N budget symbol original inherited values before fourth memo =
      .done second later currentFourth current) :
    first = second ∧ after = later ∧ savedFourth = currentFourth ∧ saved = current := by
  have left := edge_done_stable one (Nat.le_max_left g G) (Nat.le_max_left s S) (Nat.le_max_left r R)
    (Nat.le_max_left e E) (Nat.le_max_left p P) (Nat.le_max_left h H) (Nat.le_max_left m M)
    (Nat.le_max_left c C) (Nat.le_max_left n N)
  have right := edge_done_stable two (Nat.le_max_right g G) (Nat.le_max_right s S) (Nat.le_max_right r R)
    (Nat.le_max_right e E) (Nat.le_max_right p P) (Nat.le_max_right h H) (Nat.le_max_right m M)
    (Nat.le_max_right c C) (Nat.le_max_right n N)
  exact Outcome.done.inj (left.symm.trans right)

end MicroCFTA.SourceCurrentAllocatedParentWorkerStability
