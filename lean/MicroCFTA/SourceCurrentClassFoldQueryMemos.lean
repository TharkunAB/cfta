import MicroCFTA.SourceCurrentClassEditQueryMemos
import MicroCFTA.SourceCurrentClassFoldDomains

/-!
# Global memo receipts through the actual class right fold

Every head class captures the actual forest and tables returned by its tail.
Original selected path domains derive each reached capture domain. Final
literal empty propagation adds no call or heap effect. Returned tables retain
all earlier unfolding entries and both original query tables.
-/
namespace MicroCFTA.SourceCurrentClassFoldQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityProjectionPathDomain
open SourceCurrentSubsumesQueryMemos (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- The memo receipt follows the actual tail before the next head capture. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : NativeState width Symbol Guard} →
    Fold emptyGuard conjoin clear top records values before results after → Memos → Memos → Prop where
  | nil : FoldReads .nil memos memos
  | cons (tail : FoldReads actualTail memos middle)
      (head : SourceCurrentClassEditQueryMemos.ClassReads actualHead middle saved) :
      FoldReads (.cons actualTail actualHead) memos saved

/-- Final propagation retains exactly the completed fold's memo bundle. -/
inductive PassReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : NativeState width Symbol Guard} →
    Pass emptyGuard conjoin clear top records values before results after → Memos → Memos → Prop where
  | done (fold : FoldReads actual memos saved) : PassReads (.done actual) memos saved

/-- Every actual right fold derives its ordered global reads and final coherent cost and memo state. -/
theorem fold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, FoldReads actual memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  induction actual generalizing memos with
  | nil =>
      exact ⟨memos, .nil, pure_keeps _ ready.semantic.ready, ready.semantic, costs, valid, extends_refl _, rfl⟩
  | cons tail head ih =>
      have tailCoherent := fun record member => coherent record (List.mem_cons_of_mem _ member)
      have tailActive := fun record member => active record (List.mem_cons_of_mem _ member)
      have tailDomains := fun record member => domains record (List.mem_cons_of_mem _ member)
      obtain ⟨middle, tailReads, tailEffects⟩ := ih tailCoherent tailActive ready costs available tailDomains memos valid
      have tailState := SourceCurrentClassFoldDomains.fold_domains emptyGuard conjoin clear top tail
        tailCoherent tailActive ready available tailDomains
      obtain ⟨saved, headReads, headEffects⟩ := SourceCurrentClassEditQueryMemos.class_memos head
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) tailState.1 tailEffects.costs tailState.2.2.1
        (fun path member => tailState.2.2.2 _ (domains _ List.mem_cons_self path member)) middle tailEffects.valid
      exact ⟨saved, .cons tailReads headReads, SourceCurrentTargetQueryMemos.effect_trans tailEffects headEffects⟩

/-- The actual complete pass derives its final global bundle without a future coherence premise. -/
theorem pass_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, PassReads actual memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  cases actual with
  | done fold =>
      obtain ⟨saved, reads, effects⟩ := fold_memos fold coherent active ready costs available domains memos valid
      exact ⟨saved, .done reads, effects⟩

end MicroCFTA.SourceCurrentClassFoldQueryMemos
