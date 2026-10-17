import MicroCFTA.SourceCurrentAllocatedParentEdge
import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth

/-!
# Native writer history through actual parent stages

Actual native requests extend the past checked history. Physical stages
retain the complete native tables and record their actual heap growth.
The theorems use completed read graphs. They do not assume a writer law
for a future query or establish termination of the outer worker.
-/
namespace MicroCFTA.SourceCurrentParentNativeHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem physical_history {before after : Checked width} (history : History before)
    (effects : Effects (physical before) (physical after))
    (nodes : after.native.nodes = before.native.nodes)
    (edges : after.native.edges = before.native.edges)
    (domains : after.native.machine.domains = before.native.machine.domains) : History after := by
  have same : after = advancePhysical before (physical after) := by
    cases before with
    | mk first ops =>
      cases after with
      | mk last finalOps =>
        cases first with
        | mk firstMachine firstNodes firstEdges =>
          cases last with
          | mk lastMachine lastNodes lastEdges =>
            cases firstMachine with
            | mk firstHeap firstDomains =>
              cases lastMachine with
              | mk lastHeap lastDomains =>
                dsimp at nodes edges domains
                subst lastNodes
                subst lastEdges
                subst lastDomains
                rfl
  have kept : History (advancePhysical before (physical after)) :=
    history.advance (physical after) effects.keeps.growth
  exact same.symm ▸ kept

private theorem operand {formulas solver inventory path values before memo value after saved memos final}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt (width := width) formulas solver inventory
      path values before memo value after saved memos final) (history : History before) : History after :=
  physical_history history receipt.effects receipt.nodes receipt.edges receipt.domains

private theorem target_fold {formulas solver values seed paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Fold (width := width) values seed paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.FoldReads formulas solver actual memos final) :
    History before → History after ∧ Ready after := by
  induction reads with
  | nil receipt => exact fun history => ⟨operand receipt history,receipt.ready⟩
  | @cons values seed path paths before middle later after memo current saved head tail result
      memos nextMemos lastMemos inventory nextInventory first rest step receipt remaining query ih =>
    intro history
    have headHistory := operand receipt history
    obtain ⟨tailHistory,tailReady⟩ := ih headHistory
    cases step with
    | run trace => exact ⟨tailHistory.query _ _ _ tailReady.good trace,query.ready⟩

/-- Actual target reads transport the same native writer history through every reached query. -/
theorem target {formulas solver values paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Target (width := width) values paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (history : History before) : History after := by
  cases reads with
  | nil => exact history
  | cons reads => exact (target_fold reads history).1

/-- Actual slot hits and completed misses retain native history without a new slot-law premise. -/
theorem force {formulas solver inventory record values base path before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt (width := width) formulas solver inventory
      record values base path before value after memos final)
    (history : History before.checked) : History after.checked := by
  cases receipt.reads with
  | hit => exact history
  | miss absent reads => exact target reads history

/-- Actual target forcing and its following native query retain the captured earlier writers. -/
theorem leaf {formulas solver inventory record values base path input before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt (width := width) formulas solver inventory
      record values base path input before value after memos final)
    (history : History before.checked) : History after.checked := by
  cases receipt.reads with
  | apply first query =>
    have current := force first history
    cases query.actual with
    | run trace => exact current.query _ _ _ first.ready.checked.good trace

end MicroCFTA.SourceCurrentParentNativeHistory
