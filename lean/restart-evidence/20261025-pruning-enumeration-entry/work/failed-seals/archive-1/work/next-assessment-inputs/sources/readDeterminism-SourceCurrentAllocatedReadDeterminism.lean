import MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos
import MicroCFTA.SourceCurrentRequiredQueryMemos

/-!
# Actual global read receipts retain their own returned tables

Fixed-budget exposure reads have a unique returned unfolding table. This
aligns constructed correctness witnesses with the supplied exposure receipt.
Other actual reads require their own validity proof; equality of returned
heaps alone does not identify two different read schedules.
-/
namespace MicroCFTA.SourceCurrentAllocatedReadDeterminism
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A fixed-budget collection determines its returned unfolding table. -/
theorem collect_unique [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {heap : State Symbol Guard} {seen : List Nat} {pending : List (Value Symbol Guard)}
    {memos first second : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard}
    (left : SourceEqualityExposureMemos.CollectReads fuel heap seen pending memos first)
    (right : SourceEqualityExposureMemos.CollectReads fuel heap seen pending memos second) : first = second := by
  induction fuel generalizing heap seen pending memos first second with
  | zero => cases pending <;> cases left <;> cases right <;> rfl
  | succ fuel ih =>
      cases pending with
      | nil => cases left; cases right; rfl
      | cons value rest =>
          cases value <;> cases left <;> cases right <;> try simp_all
          all_goals exact ih (by assumption) (by assumption)

/-- One actual bounded row exposure determines its returned unfolding table. -/
theorem exposure_unique [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {value : Value Symbol Guard} {heap : State Symbol Guard}
    {memos first second : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard}
    (left : SourceEqualityExposureMemos.NodeEdgesReads fuel value heap memos first)
    (right : SourceEqualityExposureMemos.NodeEdgesReads fuel value heap memos second) : first = second := by
  cases value <;> cases left <;> cases right <;> try simp_all
  case union.union.union => exact collect_unique (by assumption) (by assumption)
  case mu.mu.mu =>
    rename_i entry body depth ordinary nextFirst heapFirst memoFirst actualFirst calledFirst restFirst
      nextSecond heapSecond memoSecond actualSecond calledSecond restSecond
    obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (actualFirst.symm.trans actualSecond)
    have sameMemo := congrArg Prod.snd (InternedNestedConstruction.Outcome.done.inj (calledFirst.symm.trans calledSecond)).1
    cases sameMemo
    cases nextFirst <;> dsimp only at restFirst restSecond
    all_goals first
      | exact restFirst.trans restSecond.symm
      | exact collect_unique restFirst restSecond

/-- A supplied fixed-budget exposure receipt derives its own actual final validity. -/
theorem exposure [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {value : Value Symbol Guard} {heap : State Symbol Guard} {memos final : Memos}
    (reads : SourceEqualityQueryGlobalMemos.ExposureReads fuel value heap memos final)
    (semantic : SemanticReady heap) (costs : CostHeap heap) (available : Available heap value)
    (valid : Valid heap memos) :
    Valid (MergedFreshOrdinaryExposure.nodeEdges fuel value heap).state final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨saved, actual, correct, retained⟩ := SourceEqualityQueryGlobalMemos.exposure_memos
    fuel value heap semantic costs available memos valid
  have unfolding := exposure_unique actual.1 reads.1
  have same : saved = final := by
    cases saved
    cases final
    congr 1
    exact actual.2.trans reads.2.symm
  subst saved
  exact ⟨correct, retained, reads.2⟩

end MicroCFTA.SourceCurrentAllocatedReadDeterminism
