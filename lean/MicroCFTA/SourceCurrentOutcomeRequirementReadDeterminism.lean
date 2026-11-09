import MicroCFTA.SourceEqualityProjectionOutcomeReadDeterminism
import MicroCFTA.SourceCurrentConjunctionRequirementCellsOutcomeMemos

/-!
# Exact memo bundles through deferred requirement forcing

One pending cursor determines each projection and its returned bundle.
Successful prefixes pass that exact bundle to the remaining jobs.
The same literal force outcome therefore determines its final tables.
-/
namespace MicroCFTA.SourceCurrentOutcomeRequirementReadDeterminism
open Cache InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionRequirementPull (Cursor Event step)
open SourceCurrentConjunctionRequirementPullOutcomeMemos (StepReads RunReads)
open SourceCurrentConjunctionRequirementCellsOutcomeMemos (ForceReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem step_actual {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before : Physical} {result : Outcome Symbol FullSyntax.Formula (Event Symbol FullSyntax.Formula)}
    {memos saved : Memos} (reads : StepReads p h cursor before result memos saved) :
    step p h cursor before = result := by
  cases reads with
  | finished => rfl
  | failed actual _ => exact SourceCurrentConjunctionRequirementPull.step_failed _ _ _ _ _ _ _ _ actual
  | empty actual _ => exact SourceCurrentConjunctionRequirementPull.step_empty _ _ _ _ _ _ _ actual
  | more actual nonempty _ => exact SourceCurrentConjunctionRequirementPull.step_more _ _ _ _ _ _ _ _ actual nonempty

private theorem step_unique {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before : Physical} {result : Outcome Symbol FullSyntax.Formula (Event Symbol FullSyntax.Formula)}
    {other : Outcome Symbol FullSyntax.Formula (Event Symbol FullSyntax.Formula)}
    {memos first second : Memos}
    (left : StepReads p h cursor before result memos first)
    (right : StepReads p h cursor before other memos second) : first = second := by
  cases left <;> cases right
  · rfl
  all_goals exact SourceEqualityProjectionOutcomeReadDeterminism.forest_global_unique (by assumption) (by assumption)

private theorem run_unique {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before : Physical} {result : Outcome Symbol FullSyntax.Formula (List Node)}
    {other : Outcome Symbol FullSyntax.Formula (List Node)}
    {memos first second : Memos}
    (left : RunReads p h cursor before result memos first)
    (right : RunReads p h cursor before other memos second) : first = second := by
  induction left generalizing other second with
  | complete first =>
      cases right with
      | complete last => exact step_unique first last
      | failed last => cases (step_actual first).symm.trans (step_actual last)
      | more other rest => cases (step_actual first).symm.trans (step_actual other)
  | failed first =>
      cases right with
      | failed last => exact step_unique first last
      | complete last => cases (step_actual first).symm.trans (step_actual last)
      | more other rest => cases (step_actual first).symm.trans (step_actual other)
  | more first rest ih =>
      cases right with
      | complete last => cases (step_actual first).symm.trans (step_actual last)
      | failed last => cases (step_actual first).symm.trans (step_actual last)
      | more last tail =>
          have outputs := Outcome.done.inj ((step_actual first).symm.trans (step_actual last))
          cases outputs.1
          cases outputs.2
          have same := step_unique first last
          cases same
          exact ih tail

/-- The same actual force result determines the complete returned global bundle. -/
theorem force_unique {p h handle : Nat} {before : Cells}
    {result : SourceCurrentConjunctionRequirementCells.Outcome Symbol FullSyntax.Formula (List Node)}
    {memos first second : Memos}
    (left : ForceReads p h handle before result memos first)
    (right : ForceReads p h handle before result memos second) : first = second := by
  generalize otherEq : result = other at right
  clear otherEq
  cases left <;> cases right <;> try simp_all
  all_goals exact run_unique (by assumption) (by assumption)

end MicroCFTA.SourceCurrentOutcomeRequirementReadDeterminism
