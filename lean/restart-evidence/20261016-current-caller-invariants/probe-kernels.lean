import MicroCFTA.SourceCurrentAllocatedProbeActual
import MicroCFTA.SourceCurrentAllocatedNativeTraceEffects

namespace MicroCFTA.ProbeIntegration
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "u" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches u
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem supplied_parent_clean
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt formulas solver next symbol original loaded inherited values
      before result after fourth savedFourth memo saved final ∧ ProbeHeap after.native.machine.heap ∧
      ∀ entry body depth ordinary, Available after.native.machine.heap (.mu entry body depth ordinary) →
        SourceEqualityMuReconstruction.rebuild entry body depth ordinary after.native.machine.heap =
          .done (cleanup (.mu entry body depth ordinary)) after.native.machine.heap := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory reads ready admitted live
    correct stored covered valid
  have probes := SourceCurrentAllocatedProbeParent.parent_heap formulas solver inventory reads ready admitted live
    correct stored covered valid probes
  refine ⟨next, receipt, probes, ?_⟩
  intro entry body depth ordinary available
  exact (SourceCurrentAllocatedMuRebuild.resident_rebuild after receipt.ready probes entry body depth ordinary available).1
theorem supplied_stage_same_globals
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ∃ next, SourceCurrentConjunctionScanClassPass.Receipt formulas solver next records values results before after
      fourth savedFourth memo saved outcome final ∧ Valid after.native.machine.heap final ∧
      ProbeHeap after.native.machine.heap := by
  obtain ⟨next, receipt⟩ := SourceCurrentConjunctionScanClassPassActual.verified formulas solver inventory reads ready admitted
    available proper fields correct stored covered ranges valid
  exact ⟨next, receipt, receipt.globals,
    SourceCurrentAllocatedProbeReduction.stage_heap formulas solver inventory reads ready admitted available proper fields
      correct stored covered ranges valid probes⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
theorem open_forest_projection
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityProjectionGraph.Forest path values before result after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values)
    (probes : ProbeHeap before) : ProbeHeap after :=
  SourceCurrentAllocatedProbeExposure.forest_heap actual semantic costs available probes

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
theorem required_and_residency
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard))
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (probes : ProbeHeap before) (available : Values before values) :
    ProbeHeap after ∧ Values after results ∧ SourceEqualityRequiredCache.Keeps before after := by
  have effect := SourceCurrentAllocatedProbeRequired.requireAll fuel readFuel paths values results before after done
    semantic costs probes available
  exact ⟨effect.2.2.2.1, effect.2.2.2.2, effect.1⟩

omit [DecidableEq (Value Symbol Guard)] in
theorem warm_merge_hit
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : InternedConstructorTemplates.State Symbol Guard) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard)
    (found : memo input.referenceOf = some entry)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (stored : SourceCurrentMemoMergeEffects.Stored before memo) (available : Available before input)
    (probes : ProbeHeap before) :
    SourceCurrentMemoMergeGraph.Call clear top input before memo entry.result before memo ∧ ProbeHeap before := by
  exact ⟨.hit found, SourceCurrentAllocatedProbeMerge.Merge.call_heap (clear := clear) (top := top) (.hit found) semantic costs stored available probes⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
theorem rejected_constructor_no_children
    (symbol : Symbol) (before : Checked width) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.machine.heap :=
  SourceCurrentAllocatedProbeParent.reject_heap symbol before probes

omit [DecidableEq (Value Symbol Guard)] in
theorem returned_checked_trace
    {fuel : Nat} {control : SourceEqualityNativeDemand.Control (Value Symbol Guard)} {value : Value Symbol Guard}
    {before after : Checked width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before (.code (.pure value)) after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (probes : ProbeHeap before.native.machine.heap) :
    SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
        (SourceCurrentAllocatedNativeEffects.physical after) ∧ ProbeHeap after.native.machine.heap := by
  have effects := SourceCurrentAllocatedNativeTraceEffects.effects trace good semantic costs fields
  exact ⟨effects.1, effects.2.1, SourceCurrentAllocatedMuRebuild.trace_heap trace semantic probes⟩

#check SourceCurrentAllocatedProbeParent.local_finite
#check SourceCurrentAllocatedProbeParent.parent_finite
#check SourceCurrentAllocatedProbeClassPass.pass_complete
#check SourceCurrentAllocatedProbeTargets.force_heap
#check SourceCurrentAllocatedProbeTargets.leaf_heap

omit [DecidableEq (Value Symbol Guard)] in
theorem supplied_pass_conditional_exact
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : SourceCurrentAllocatedClassPass.Pass records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ∃ next, SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final ∧
      ProbeHeap after.native.machine.heap ∧
      ∀ ambient symbol terms, (∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
        (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory reads coherent active
    ready admitted available domains stored covered valid
  exact ⟨next, receipt,
    SourceCurrentAllocatedProbeClassPass.pass_heap formulas solver inventory reads coherent active ready admitted available domains
      stored covered valid probes, fun ambient symbol terms satisfied => (receipt.language ambient symbol terms).2 satisfied⟩

end MicroCFTA.ProbeIntegration
