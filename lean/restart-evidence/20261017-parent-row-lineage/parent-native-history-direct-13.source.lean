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

private theorem edit_children_aux {formulas solver base record originals entries offset values before results after memos final}
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

/-- Actual selected children retain history and constructor validity at their exact returned heap. -/
theorem edit_children {formulas solver base record originals entries offset values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditChildren (width := width) record originals entries offset values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ChildrenReads formulas solver base actual memos final)
    (history : History before.checked) (valid : Valid before.checked.native.machine.heap) :
    History after.checked ∧ Valid after.checked.native.machine.heap :=
  edit_children_aux reads history valid

/-- An actual row prefix retains history through its ordered child calls and literal edge construction. -/
theorem edit_rows {formulas solver base record originals entries edges before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditRows (width := width) record originals entries edges before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.RowsReads formulas solver base actual memos final)
    (history : History before.checked) (valid : Valid before.checked.native.machine.heap) :
    History after.checked ∧ Valid after.checked.native.machine.heap := by
  have maintained : Maintained before after := by
    refine SourceCurrentAllocatedSharedEditGraph.RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} _ _ _ _ => True)
      (motive_2 := fun {record originals entries offset values before results after} _ _ _ _ => True)
      (motive_3 := fun {record originals entries edges before results after} _ _ _ _ => Maintained before after)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ reads
    · intro record originals entries state memos history valid
      exact ⟨history,valid⟩
    · intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest firstRead restRead ignored ih history valid
      obtain ⟨current,currentValid⟩ := edit_children_aux firstRead history valid
      have construction := run_correct (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap currentValid
      rw [rebuilt] at construction
      exact ih (current.advance _ construction.2) construction.1
  exact maintained history valid

/-- Actual node reads retain history through a recursive head and all reconstructed rows. -/
theorem edit_node {formulas solver base record originals edits value before result after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditNode (width := width) record originals edits value before result after}
    (reads : SourceCurrentAllocatedSharedEditGraph.NodeReads formulas solver base actual memos final)
    (history : History before.checked) (valid : Valid before.checked.native.machine.heap) :
    History after.checked ∧ Valid after.checked.native.machine.heap := by
  have maintained : Maintained before after := by
    refine SourceCurrentAllocatedSharedEditGraph.NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} _ _ _ _ => Maintained before after)
      (motive_2 := fun {record originals entries offset values before results after} _ _ _ _ => True)
      (motive_3 := fun {record originals entries edges before results after} _ _ _ _ => True)
      ?_ ?_ ?_ ?_ (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial) reads
    · intro next record originals path value before result after memos saved receipt history valid
      exact ⟨leaf receipt history,receipt.ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid⟩
    · intro record originals entries state memos history valid
      exact ⟨history,valid⟩
    · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ignored history valid
      obtain ⟨current,currentValid⟩ := edit_rows read history valid
      have construction := run_correct (makeNode rebuilt) middle.checked.native.machine.heap currentValid
      rw [built] at construction
      exact ⟨current.advance _ construction.2,construction.1⟩
    · intro record originals memos current saved entries original before exposed heap value after recursive head body headRead headGlobal bodyRead ih history valid
      exact ih (history.advance _ headGlobal.keeps.growth)
        headGlobal.semantic.ready.semantic.1.normal.facts.coherent.valid
  exact maintained history valid

private theorem edit_list {formulas solver base record originals edits values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditList (width := width) record originals edits values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver base actual memos final) :
    Maintained before after := by
  cases reads with
  | leaf => exact fun history valid => ⟨history,valid⟩
  | children read => exact edit_children_aux read

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
  letI : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _
  obtain ⟨chosen,returned,produced,good,effects,extension,scopes,idle,available,closed⟩ :=
    SourceCurrentAllocatedSeededQuery.operand_complete unconstrained anchor anchorSemantic anchorReady path values before
      ready.good (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
      ready.scopedCache ready.idle available growth supported
  obtain ⟨rfl,rfl⟩ := actual.unique produced
  exact ⟨⟨good,effects.ready.semantic,effects.ready.costs,scopes,idle⟩,effects⟩

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
    exact physical_history history facts.2 (by cases operand; rfl) (by cases operand; rfl) (by cases operand; rfl)
  | cons operand rest trace ih =>
    intro history ready available growth supported ranges
    cases ranges with
    | cons tailRanges nativeRanges =>
      have first := seeded_operand anchorSemantic anchorReady operand ready available growth (supported _ List.mem_cons_self)
      have currentHistory := physical_history history first.2
        (by cases operand; rfl) (by cases operand; rfl) (by cases operand; rfl)
      have tailAvailable := fun original member => first.2.keeps.available original (available original member)
      have tailGrowth := grows_trans growth first.2.keeps.growth
      have tailSupported := fun path member => supported path (List.mem_cons_of_mem _ member)
      have tailHistory := ih currentHistory first.1 tailAvailable tailGrowth tailSupported (tailRanges _ _ operand)
      obtain ⟨chosen,returned,produced,good,effects,extension,scopes,idle,resident,closed⟩ :=
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
    apply seeded_fold (unconstrained := unconstrained) anchorSemantic anchorReady actual history ready available growth _ ranges
    intro path member
    rcases List.mem_append.mp member with included | included
    · exact supported path (List.mem_cons_of_mem _ included)
    · have same := List.mem_singleton.mp included
      subst path
      exact supported _ List.mem_cons_self

private theorem false_seeded {unconstrained paths values before anchor query middle}
    (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths
      before.native.machine.heap false anchor)
    (actual : SourceCurrentAllocatedSeededQuery.Seeded (width := width) values (paths.map (List.map Int.ofNat))
      (SourceCurrentConjunctionClassScan.advanceHeap before anchor) query middle)
    (history : History before) (ready : Ready before)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (SourceCurrentConjunctionClassScan.advanceHeap before anchor)) :
    History middle ∧ Ready middle ∧ Effects (physical before) (physical middle) ∧
      Available middle.native.machine.heap query := by
  have second := SourceCurrentConjunctionClassScan.secondary_effects unconstrained secondary ready available
  obtain ⟨anchorSemantic,anchorReady,keeps,anchorAvailable,support⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained secondary ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have anchorHistory := history.advance _ second.2.1.keeps.growth
  have queryHistory := seeded anchorSemantic anchorReady actual anchorHistory second.1 anchorAvailable
    (grows_refl anchor) (by
      intro path member
      obtain ⟨original,found,rfl⟩ := List.mem_map.mp member
      exact support original found) ranges
  obtain ⟨chosen,returned,produced,good,effects,extension,scopes,idle,resident,closed⟩ :=
    SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values secondary
      ready.good (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
      ready.scopedCache ready.idle available proper ranges
  obtain ⟨rfl,rfl⟩ := actual.unique produced
  exact ⟨queryHistory,⟨good,effects.ready.semantic,effects.ready.costs,scopes,idle⟩,effects,resident⟩

variable [DecidableEq (Value Symbol Guard)]

private theorem scan {formulas solver budget unconstrained reaches values classes before fourth outcome selected after saved}
    (actual : SourceCurrentConjunctionClassScan.Scan (width := width) budget unconstrained reaches values
      classes before fourth outcome selected after saved) :
    ∀ (history : History before) (ready : Ready before)
      (available : InternedNestedProvenance.Values before.native.machine.heap values)
      (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
      (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
      (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before fourth),
      History after ∧ Ready after ∧ Effects (physical before) (physical after) ∧
        InternedNestedProvenance.Values after.native.machine.heap values ∧
        SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved := by
  induction actual with
  | nil =>
    intro history ready available proper correct ranges
    exact ⟨history,ready,.refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),available,correct⟩
  | selected primary rest ih =>
    intro history ready available proper correct ranges
    have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
    have current := history.advance _ first.2.1.keeps.growth
    have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
    obtain ⟨finalHistory,finalReady,effects,finalAvailable,finalCorrect⟩ := ih current first.1 first.2.2
      (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect (ranges.1 _ primary)
    exact ⟨finalHistory,finalReady,first.2.1.trans effects,finalAvailable,finalCorrect⟩
  | skipped primary secondary rest ih =>
    intro history ready available proper correct ranges
    have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
    have second := SourceCurrentConjunctionClassScan.secondary_effects unconstrained secondary first.1 first.2.2
    have current := (history.advance _ first.2.1.keeps.growth).advance _ second.2.1.keeps.growth
    have effects := first.2.1.trans second.2.1
    have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps _ correct
    obtain ⟨finalHistory,finalReady,later,finalAvailable,finalCorrect⟩ := ih current second.1 second.2.2
      (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect (ranges.2.1 _ primary _ secondary)
    exact ⟨finalHistory,finalReady,effects.trans later,finalAvailable,finalCorrect⟩
  | continued primary secondary query decision rest ih =>
    intro history ready available proper correct ranges
    have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
    have reached := ranges.2.2 _ primary _ secondary
    obtain ⟨queryHistory,queryReady,queryEffects,queryAvailable⟩ := false_seeded secondary query
      (history.advance _ first.2.1.keeps.growth) first.1 first.2.2 (proper _ List.mem_cons_self) reached.1
    have effects := first.2.1.trans queryEffects
    have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps _ correct
    obtain ⟨memoReady,memoEffects,memoCorrect,sound,retained⟩ :=
      SourceCurrentConjunctionClassScan.memo_effects formulas solver decision queryReady queryAvailable queryCorrect
    have memoHistory := queryHistory.advance _ memoEffects.keeps.growth
    have allEffects := effects.trans memoEffects
    have allAvailable := fun value member => allEffects.keeps.available value (available value member)
    obtain ⟨finalHistory,finalReady,later,finalAvailable,finalCorrect⟩ := ih memoHistory memoReady allAvailable
      (fun paths member => proper paths (List.mem_cons_of_mem _ member)) memoCorrect (reached.2 _ _ query _ _ decision)
    exact ⟨finalHistory,finalReady,allEffects.trans later,finalAvailable,finalCorrect⟩
  | stopped primary secondary query decision =>
    intro history ready available proper correct ranges
    have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
    have reached := ranges.2.2 _ primary _ secondary
    obtain ⟨queryHistory,queryReady,queryEffects,queryAvailable⟩ := false_seeded secondary query
      (history.advance _ first.2.1.keeps.growth) first.1 first.2.2 (proper _ List.mem_cons_self) reached.1
    have effects := first.2.1.trans queryEffects
    have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps _ correct
    obtain ⟨memoReady,memoEffects,memoCorrect,sound,retained⟩ :=
      SourceCurrentConjunctionClassScan.memo_effects formulas solver decision queryReady queryAvailable queryCorrect
    have allEffects := effects.trans memoEffects
    exact ⟨queryHistory.advance _ memoEffects.keeps.growth,memoReady,allEffects,
      fun value member => allEffects.keeps.available value (available value member),memoCorrect⟩

private theorem continuation {formulas solver budget records values before fourth memo outcome results after savedFourth saved memos final}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction (width := width) budget records values before fourth memo outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPass.Reads formulas solver actual memos final)
    (history : History before) (ready : Ready before)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (proper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth) :
    History after ∧ Valid after.native.machine.heap := by
  cases reads with
  | stopped first =>
    rename_i paths selected actual
    have result := scan actual history ready available proper correct ranges
    exact ⟨result.1,result.2.1.semantic.ready.semantic.1.normal.facts.coherent.valid⟩
  | completed first second last =>
    rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required actual retained pass
    obtain ⟨current,currentReady,effects,currentAvailable,currentCorrect⟩ := scan actual history ready available proper correct ranges
    have requiredEffects := SourceCurrentRequiredHeapEffects.requireAll
      (SourceCurrentConjunctionEquality.FieldAvailable middle.operations) fuel readFuel _ values requiredValues
      middle.native.machine.heap heap required currentReady.semantic currentReady.costs currentReady.good.fields currentAvailable
    have requiredHistory := current.advance _ requiredEffects.1.growth
    cases last with
    | done read => exact class_fold read requiredHistory requiredEffects.2.1.ready.semantic.1.normal.facts.coherent.valid

private theorem local_reduction {formulas solver inventory budget original loaded inherited values before fourth memo results after savedFourth saved memos final}
    {actual : SourceCurrentAllocatedLocalReduction.Reduction (width := width) budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : SourceCurrentAllocatedLocalReduction.Reads formulas solver actual memos final)
    (history : History before) (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo) :
    History after ∧ Valid after.native.machine.heap := by
  obtain ⟨own,branch,checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory before
    ready admitted original cached loaded found inherited inheritedReady
  have current : History (SourceCurrentAllocatedPrecheck.state before loaded inherited) :=
    history.advance _ (grows_refl before.native.machine.heap)
  cases reads with
  | unchanged => exact ⟨current,ready.semantic.ready.semantic.1.normal.facts.coherent.valid⟩
  | emptyChildren => exact ⟨current,ready.semantic.ready.semantic.1.normal.facts.coherent.valid⟩
  | classes read =>
    rename_i records outcome actual next
    have same : branch = .classes records := Except.ok.inj (checked.actual.symm.trans actual)
    subst branch
    exact continuation read current checked.ready available (checked.classes records rfl).1 correct (ranges records actual).scan

private theorem built_history {symbol loaded children before result after}
    (built : SourceCurrentAllocatedMkEdge.build (width := width) symbol loaded children before = (.ok result,after))
    (history : History before) (valid : Valid before.native.machine.heap) : History after := by
  unfold SourceCurrentAllocatedMkEdge.build SourceEqualityMkEdgeAllocation.build at built
  cases checked : (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).1 with
  | error message => simp only [checked] at built; cases built
  | ok keep =>
    simp only [checked] at built
    have growth := (run_correct
      (SourceEqualityMkEdgeAllocation.work symbol (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children keep)
      before.native.machine.heap valid).2
    obtain ⟨resultEq,stateEq⟩ := Prod.mk.inj built
    subst after
    exact history.advance _ growth

/-- A completed Parent graph retains native writers through the actual Scan, Required, class pass, and constructor.
The range premise is the existing initial Parent range plan. Class-pass transport does not require it. -/
theorem parent {formulas solver inventory budget symbol original loaded inherited values before fourth memo result after savedFourth saved memos final}
    {actual : SourceCurrentAllocatedParentEdge.Edge (width := width) budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdge.Reads formulas solver actual memos final)
    (history : History before) (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original loaded inherited values before fourth memo) :
    History after := by
  cases reads with
  | rejected =>
    exact history.advance _ (run_correct (makeEdge symbol SourceEqualityPCSGuard.top [.empty])
      before.native.machine.heap ready.semantic.ready.semantic.1.normal.facts.coherent.valid).2
  | live lower =>
    rename_i children middle test built reduction
    obtain ⟨current,currentValid⟩ := local_reduction lower history ready admitted cached found inheritedReady available correct (ranges test)
    exact built_history built current currentValid

end MicroCFTA.SourceCurrentParentNativeHistory
