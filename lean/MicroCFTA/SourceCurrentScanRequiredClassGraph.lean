import MicroCFTA.SourceCurrentScanRequiredNumeric
import MicroCFTA.SourceCurrentConjunctionScanClassPassActual

/-!
# Actual class graphs from complete preparation

The preparation reads retain the original Scan and Required execution.
Their reached branch constructs the existing complete class graph.
The prepared branch passes its exact returned global memos to the pass.
-/
namespace MicroCFTA.SourceCurrentScanRequiredClassGraph
open InternedConstructorTemplates EqualityNormalize SourceEqualityClassOrder
open SourceCurrentConjunctionScanClassPass (Reduction)
namespace Preparation
export SourceCurrentScanRequiredNumeric (Execution Reads)
end Preparation
namespace Actual
export SourceCurrentConjunctionScanClassPassActual (Reads)
end Actual
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width budget : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A stopped preparation constructs the existing stopped graph with the same strict reads. -/
theorem stopped {records kept : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth saved : Fourth} {memo : Memo} {paths : Class} {memos final : Memos}
    {actual : Preparation.Execution budget records values before fourth (some paths) kept results after saved}
    (reads : Preparation.Reads actual memos final) :
    ∃ graph : Reduction budget records values before fourth memo (some paths) results after saved memo,
      Actual.Reads formulas solver graph memos final := by
  cases reads with
  | stopped first => exact ⟨.stopped (by assumption), .stopped first⟩

/-- The actual pass continues the exact prepared heap, records, and global memo bundle. -/
theorem completed {records kept : List Record} {values prepared results : List (Value Symbol Guard)}
    {before middle after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {memos current final : Memos}
    {actual : Preparation.Execution budget records values before fourth none kept prepared middle savedFourth}
    (reads : Preparation.Reads actual memos current)
    (pass : SourceCurrentAllocatedClassPass.Pass kept prepared middle memo results after saved)
    (last : SourceCurrentAllocatedClassPass.PassReads formulas solver pass current final) :
    ∃ graph : Reduction budget records values before fourth memo none results after savedFourth saved,
      Actual.Reads formulas solver graph memos final := by
  cases reads with
  | prepared first second =>
      refine ⟨.completed (by assumption) (by assumption) (by assumption) pass, ?_⟩
      exact .completed (retained := by assumption) (required := by assumption) first second last

end MicroCFTA.SourceCurrentScanRequiredClassGraph
