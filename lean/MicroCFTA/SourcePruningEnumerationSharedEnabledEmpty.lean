import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionTupleBudget
import MicroCFTA.SourceEndpointMemo

/-!
# Shared conjunction checks after the descendant memo

The descendant memo runs first. A false answer skips the conjunction call.
A true answer retains the complete checked shared outcome. This includes
the private snapshot on success and failure. The query memo advances in
both branches. The older Demand caller remains a separate definition.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Worker" => SourceCurrentAllocatedSharedConjunctionWorker.call
local notation "budget" => SourceCurrentConjunctionTupleBudget.currentTupleBudget
variable {width : Nat}

/-- A skipped check has no conjunction observation. A performed check retains it. -/
inductive Outcome (width : Nat) : Type 1 where
  | skipped (checked : Checked width) (memo : Fourth)
  | performed (observed : SourceCurrentAllocatedSharedConjunctionWorker.Outcome width)

/-- Execute the actual descendant memo and then the enabled shared call. -/
noncomputable def check
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries : Queries) : Outcome width × Queries :=
  let guardResult : Bool × Queries := SourceEndpointMemo.run query queries
  if guardResult.1 then
    (.performed (Worker p h budget query before memo), guardResult.2)
  else (.skipped before memo, guardResult.2)

/-- A false descendant answer leaves the checked state and fourth memo exact. -/
theorem check_skipped
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries saved : Queries) (gate : SourceEndpointMemo.run query queries = (false, saved)) :
    check p h query before memo queries = (.skipped before memo, saved) := by
  simp only [check, gate, Bool.false_eq_true, ↓reduceIte]

/-- A true descendant answer retains the literal four-field shared outcome. -/
theorem check_performed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries saved : Queries) (gate : SourceEndpointMemo.run query queries = (true, saved)) :
    check p h query before memo queries = (.performed (Worker p h budget query before memo), saved) := by
  simp only [check, gate, ↓reduceIte]

/-- Every performed observation recovers its own enabled call and actual query-memo result. -/
theorem check_performed_receipt
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries saved : Queries) (observed : SourceCurrentAllocatedSharedConjunctionWorker.Outcome width)
    (actual : check p h query before memo queries = (.performed observed, saved)) :
    SourceEndpointMemo.run query queries = (true, saved) ∧
      Worker p h budget query before memo = observed := by
  cases gate : SourceEndpointMemo.run query queries with
  | mk reached guardSaved =>
    cases reached with
    | false => simp [check, gate] at actual
    | true =>
      have same : Worker p h budget query before memo = observed ∧ guardSaved = saved := by
        simpa [check, gate] using actual
      exact ⟨congrArg (Prod.mk true) same.2, same.1⟩

/-- Every skipped observation recovers the false gate and exact retained caller fields. -/
theorem check_skipped_receipt
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before after : Checked width) (memo retained : Fourth)
    (queries saved : Queries)
    (actual : check p h query before memo queries = (.skipped after retained, saved)) :
    SourceEndpointMemo.run query queries = (false, saved) ∧ after = before ∧ retained = memo := by
  cases gate : SourceEndpointMemo.run query queries with
  | mk reached guardSaved =>
    cases reached with
    | false =>
      have same : (before = after ∧ memo = retained) ∧ guardSaved = saved := by
        simpa [check, gate] using actual
      exact ⟨congrArg (Prod.mk false) same.2, same.1.1.symm, same.1.2.symm⟩
    | true => simp [check, gate] at actual

end MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
