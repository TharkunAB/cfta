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
    | run trace => exact ⟨tailHistory.query ⟨IntersectionEmptyDomain.emptyDomain,_,_⟩ _ _ tailReady.good trace,query.ready⟩

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
    | run trace => exact current.query ⟨IntersectionEmptyDomain.emptyDomain,_,_⟩ _ _ first.ready.checked.good trace

private def Maintained (before after : Shared width) : Prop :=
  History before.checked → Valid before.checked.native.machine.heap →
    History after.checked ∧ Valid after.checked.native.machine.heap

private theorem edit_children {formulas solver base record originals entries offset values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditChildren (width := width) record originals entries offset values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ChildrenReads formulas solver base actual memos final) :
    Maintained before after := by
  refine SourceCurrentAllocatedSharedEditGraph.ChildrenReads.rec
    (motive_1 := fun {record originals edits value before result after} _ _ _ _ => Maintained before after)
    (motive_2 := fun {record originals entries offset values before results after} _ _ _ _ => Maintained before after)
    (motive_3 := fun {record originals entries edges before results after} _ _ _ _ => Maintained before after)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path value before result after memos saved receipt history valid
    exact ⟨leaf receipt history,receipt.ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid⟩
  · intro record originals entries state memos history valid
    exact ⟨history,valid⟩
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih history valid
    obtain ⟨current,currentValid⟩ := ih history valid
    have construction := run_correct (makeNode rebuilt) middle.checked.native.machine.heap currentValid
    rw [built] at construction
    exact ⟨current.advance _ construction.2,construction.1⟩
  · intro record originals memos current saved entries original before exposed heap value after recursive head body headRead headGlobal bodyRead ih history valid
    exact ih (history.advance _ headGlobal.keeps.growth)
      headGlobal.semantic.ready.semantic.1.normal.facts.coherent.valid
  · intro record originals entries offset state memos history valid
    exact ⟨history,valid⟩
  · intro record originals memos saved entries values before results after value offset absent rest read ih history valid
    exact ih history valid
  · intro record originals memos current saved entries edits value before result middle values results after offset found first rest firstRead restRead firstIH restIH history valid
    obtain ⟨current,currentValid⟩ := firstIH history valid
    exact restIH current currentValid
  · intro record originals entries state memos history valid
    exact ⟨history,valid⟩
  · intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest firstRead restRead firstIH restIH history valid
    obtain ⟨current,currentValid⟩ := firstIH history valid
    have construction := run_correct (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
      middle.checked.native.machine.heap currentValid
    rw [rebuilt] at construction
    exact restIH (current.advance _ construction.2) construction.1

private theorem edit_list {formulas solver base record originals edits values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditList (width := width) record originals edits values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver base actual memos final) :
    Maintained before after := by
  cases reads with
  | leaf => exact fun history valid => ⟨history,valid⟩
  | children read => exact edit_children read

private theorem class_read {formulas solver record values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record values before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final)
    (history : History before) (valid : Valid before.native.machine.heap) :
    History after ∧ Valid after.native.machine.heap := by
  cases reads with
  | edit lower => exact edit_list lower history valid

private theorem class_fold {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final) :
    History before → Valid before.native.machine.heap → History after ∧ Valid after.native.machine.heap := by
  induction reads with
  | nil => exact fun history valid => ⟨history,valid⟩
  | cons first last ih =>
    intro history valid
    obtain ⟨current,currentValid⟩ := ih history valid
    exact class_read last current currentValid

/-- A complete actual class pass transports history through every reached leaf and reconstruction. -/
theorem class_pass {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final)
    (history : History before) (ready : Ready before) : History after := by
  cases reads with
  | done read => exact (class_fold read history ready.semantic.ready.semantic.1.normal.facts.coherent.valid).1

private theorem seeded_operand {unconstrained anchor path values before value after}
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (actual : SourceCurrentAllocatedSeededQuery.Operand (width := width) path values before value after)
    (ready : Ready before) (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (growth : Grows anchor before.native.machine.heap)
    (supported : SourceCurrentSecondaryProjectionScoped.PathSupport unconstrained anchor path values) :
    Ready after ∧ Effects (physical before) (physical after) := by
  obtain ⟨chosen,returned,produced,good,effects,extension,scoped,idle,available,closed⟩ :=
    SourceCurrentAllocatedSeededQuery.operand_complete unconstrained anchor anchorSemantic anchorReady path values before
      ready.good (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
      ready.scopedCache ready.idle available growth supported
  obtain ⟨rfl,rfl⟩ := actual.unique produced
  exact ⟨⟨good,effects.ready.semantic,effects.ready.costs,scoped,idle⟩,effects⟩

private theorem seeded_fold {unconstrained anchor values paths before value after}
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (actual : SourceCurrentAllocatedSeededQuery.Fold (width := width) values paths before value after) :
    ∀ (history : History before) (ready : Ready before)
      (available : InternedNestedProvenance.Values before.native.machine.heap values)
      (growth : Grows anchor before.native.machine.heap)
      (supported : ∀ path ∈ paths, SourceCurrentSecondaryProjectionScoped.PathSupport unconstrained anchor path values)
      (ranges : SourceCurrentAllocatedSeededQuery.FoldRanges values paths before), History after := by
  induction actual with
  | one operand =>
    intro history ready available growth supported ranges
    have facts := seeded_operand anchorSemantic anchorReady operand ready available growth (supported _ List.mem_cons_self)
    cases operand with
    | force result heap projection => exact history.advance _ facts.2.keeps.growth
  | cons operand rest trace ih =>
    intro history ready available growth supported ranges
    cases ranges with
    | cons tailRanges nativeRanges =>
      have first := seeded_operand anchorSemantic anchorReady operand ready available growth (supported _ List.mem_cons_self)
      have currentHistory : History _ := by
        cases operand with
        | force result heap projection => exact history.advance _ first.2.keeps.growth
      have tailAvailable := fun original member => first.2.keeps.available original (available original member)
      have tailGrowth := grows_trans growth first.2.keeps.growth
      have tailSupported := fun path member => supported path (List.mem_cons_of_mem _ member)
      have tailHistory := ih currentHistory first.1 tailAvailable tailGrowth tailSupported (tailRanges _ _ operand)
      obtain ⟨chosen,returned,produced,good,effects,extension,scoped,idle,resident,closed⟩ :=
        SourceCurrentAllocatedSeededQuery.fold_complete unconstrained anchor anchorSemantic anchorReady values _ _
          (tailRanges _ _ operand) first.1.good first.2.ready first.1.scopedCache first.1.idle
          tailAvailable tailGrowth tailSupported
      obtain ⟨rfl,rfl⟩ := rest.unique produced
      exact tailHistory.query ⟨IntersectionEmptyDomain.emptyDomain,_,_⟩ _ _ good trace

private theorem seeded {unconstrained anchor values paths before value after}
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (actual : SourceCurrentAllocatedSeededQuery.Seeded (width := width) values paths before value after)
    (history : History before) (ready : Ready before)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, SourceCurrentSecondaryProjectionScoped.PathSupport unconstrained anchor path values)
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values paths before) : History after := by
  cases actual with
  | nil => exact history
  | nonempty actual =>
    apply seeded_fold anchorSemantic anchorReady actual history ready available growth _ ranges
    intro path member
    rcases List.mem_append.mp member with included | included
    · exact supported path (List.mem_cons_of_mem _ included)
    · have same := List.mem_singleton.mp included
      subst path
      exact supported _ List.mem_cons_self

end MicroCFTA.SourceCurrentParentNativeHistory
