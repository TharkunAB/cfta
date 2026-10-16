import MicroCFTA.SourceEqualityOriginalAllocationPreparation
import MicroCFTA.SourceCurrentAllocatedNativeConstructedHistory

/-!
# Complete native histories after literal field preparation

The serial field program constructs its own causal allocation history.
Original construction and that history derive the initial query invariants.
The query uses the actual returned equality interner. Only its modeled
completed operation tables start empty. No source global reset is asserted.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePreparedHistory
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

/-- Literal field preparation derives the earlier history and complete exact native execution. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (initialCache : Cache.State Key) (initialValid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (pairs : List Query)
    (available : Values heap (SourceCurrentAllocatedNativeColdHistoryExact.operands pairs))
    (closed : ∀ operand ∈ SourceCurrentAllocatedNativeColdHistoryExact.operands pairs, operand.free = [])
    (ranges : WordRanges (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial
        (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initialCache).2⟩ : Checked width)) :
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initialCache fields
      (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initialCache).2 ∧
      ∃ inputs : FiniteInput (view heap (SourceEqualityPCSGuard.holds formulas solver)), ∃ fuel values after,
        SourceCurrentAllocatedNativeWarmHistory.Receipt heap formulas solver inputs fuel pairs
          (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial
            (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initialCache).2⟩ : Checked width)
          values after := by
  obtain ⟨fields, finalCache, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initialCache initialValid cached
  have sameCache :
      (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initialCache).2 = finalCache :=
    congrArg Prod.snd prepared.done
  have finalRanges : WordRanges (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial finalCache⟩ : Checked width) := by
    simpa only [sameCache] using ranges
  obtain ⟨inputs, fuel, values, after, receipt⟩ := SourceCurrentAllocatedNativeConstructedHistory.query_complete
    prepared.history initialValid expression (fun _ member => member) value heap built formulas solver pairs available closed finalRanges
  refine ⟨fields, ?_, inputs, fuel, values, after, ?_⟩
  · simpa only [sameCache] using prepared
  · simpa only [sameCache] using receipt

end MicroCFTA.SourceCurrentAllocatedNativePreparedHistory
