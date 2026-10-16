import MicroCFTA.SourceCurrentAllocatedProbeActual
import MicroCFTA.SourceCurrentAllocatedPartialFrames
import MicroCFTA.SourceCurrentAllocatedPartialSourceReads

namespace MicroCFTA.ParentActualProbeIntegration
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
local notation "prefix" => SourceCurrentAllocatedPrecheck.state
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}


/-- Both receipts describe the same supplied raw parent return and complete global bundle. -/
theorem same_parent_return
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo
      result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads F S actual memos final)
    (ready : Ready before) (admitted : At F S inventory before)
    (live : SourceEqualityMkEdgeAllocation.contradictory original=false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints=.ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.native.machine.heap) :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt F S next symbol original loaded inherited values before result after
      fourth savedFourth memo saved final ∧ InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap ∧
      SourceCurrentAllocatedParentEdge.Reads F S actual memos final := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified F S inventory reads ready admitted
    live correct stored covered valid
  have finalProbes := SourceCurrentAllocatedProbeParent.parent_heap F S inventory reads ready admitted
    live correct stored covered valid probes
  exact ⟨next, receipt, finalProbes, reads.erase⟩

/-- Actual outer edge calls preserve an independently running node cell. -/
example {budget : Nat} {request : SourceCurrentAllocatedPartialState.EdgeRequest}
    {before after : SourceCurrentAllocatedPartialState.State width} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after)
    (protocol : SourceCurrentAllocatedPartialFrames.Protocol before) (handle : Nat)
    (owner : SourceCurrentAllocatedPartialState.NodeRequest)
    (running : before.nodeResults.cells handle=some ⟨owner,.evaluating⟩) :
    after.nodeResults.cells handle=some ⟨owner,.evaluating⟩ :=
  (SourceCurrentAllocatedPartialFrames.edge_call actual protocol).node_running handle owner running

/-- Source erasure keeps the exact completed outer edge trace and global endpoints. -/
example {F : SourceGuards.Formulas FullSyntax.Formula} {S : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {request : SourceCurrentAllocatedPartialState.EdgeRequest}
    {before after : SourceCurrentAllocatedPartialState.State width} {result : EdgeValue Symbol Guard}
    {actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after}
    {memos final : Memos}
    (reads : SourceCurrentAllocatedPartialSourceReads.EdgeCallReads F S actual memos final) :
    SourceCurrentAllocatedPartialReads.EdgeCallReads F S actual memos final :=
  SourceCurrentAllocatedPartialSourceReads.edge_call_erase reads

#print axioms same_parent_return
#check @same_parent_return
end MicroCFTA.ParentActualProbeIntegration
