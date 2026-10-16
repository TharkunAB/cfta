import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory
import MicroCFTA.SourceCurrentAllocatedNativeColdHistoryExact

/-!
# Complete native queries after original construction and field history

One covered earlier allocation history supplies the equality field cache.
Actual original construction supplies the heap and its semantic invariants.
Closed available query operands derive their original syntax and model.
Only reached machine ranges remain a query execution premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeConstructedHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard
local notation "Key" => SourceEqualityPartialConstraintKey.Key
variable {width : Nat}

/-- Actual construction and a covered field history derive complete exact serial native queries. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initialCache finalCache originals)
    (initialValid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (pairs : List Query)
    (available : Values heap (SourceCurrentAllocatedNativeColdHistoryExact.operands pairs))
    (closed : ∀ operand ∈ SourceCurrentAllocatedNativeColdHistoryExact.operands pairs, operand.free = [])
    (ranges : WordRanges (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial finalCache⟩ : Checked width)) :
    ∃ inputs : FiniteInput (view heap (SourceEqualityPCSGuard.holds formulas solver)), ∃ fuel values after,
      SourceCurrentAllocatedNativeWarmHistory.Receipt heap formulas solver inputs fuel pairs
        (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial finalCache⟩ : Checked width)
        values after := by
  obtain ⟨good, semantic, _, _, _⟩ := SourceCurrentAllocatedNativeOriginalHistory.constructed
    width history initialValid expression covered value heap built
  have originals : ∀ operand ∈ SourceCurrentAllocatedNativeColdHistoryExact.operands pairs, Original operand := by
    intro operand member
    exact SourceRecursiveIntersectionOriginalOutput.closed_original operand heap good.native.machine.1.coherent
      (available operand member) (closed operand member)
  obtain ⟨fuel, values, after, receipt⟩ := SourceCurrentAllocatedNativeColdHistoryExact.cold_complete
    formulas solver ⟨heap, Cache.emptyState⟩ (SourceEqualityConstraintMemoAllocation.initial finalCache)
    good semantic pairs originals available closed ranges
  exact ⟨_, fuel, values, after, receipt⟩

end MicroCFTA.SourceCurrentAllocatedNativeConstructedHistory
