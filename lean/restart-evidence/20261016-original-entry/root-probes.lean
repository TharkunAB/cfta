import MicroCFTA.SourceCurrentAllocatedNativePreparedHistory

open MicroCFTA
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard
local notation "Key" => SourceEqualityPartialConstraintKey.Key

#check SourceCurrentAllocatedNativeConstructedHistory.query_complete
#check SourceCurrentAllocatedNativePreparedHistory.query_complete
#print axioms SourceCurrentAllocatedNativeConstructedHistory.query_complete
#print axioms SourceCurrentAllocatedNativePreparedHistory.query_complete

namespace MicroCFTA.OriginalEntryKernelProbe
variable {width : Nat}

theorem prepared_actual_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    let before : Checked width := ⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial
      (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initialCache).2⟩
    ∃ fuel values after,
      execute (fuel + 1) (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs)) before = .done values after ∧
      (∀ extra, execute (fuel + extra + 1) (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs)) before = .done values after) ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧
      SourceEqualityRequiredSemanticCache.SemanticReady after.native.machine.heap ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧ SourceRecursiveIntersectionNative.Idle after.native ∧
      (∀ result ∈ values, Available after.native.machine.heap result ∧ result.free = []) ∧
      All₂ (fun pair result => ∀ output term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.1 term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.2 term) pairs values ∧
      All₂ (fun pair result => ∀ key,
        SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key →
          execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2)) after = .done result after) pairs values := by
  obtain ⟨fields, prepared, inputs, fuel, values, after, receipt⟩ := SourceCurrentAllocatedNativePreparedHistory.query_complete
    initialCache initialValid expression cached value heap built formulas solver pairs available closed ranges
  refine ⟨fuel, values, after, receipt.done, ?_, receipt.good, receipt.semantic, receipt.scopedCache, receipt.idle,
    (fun result member => ⟨receipt.result result member, receipt.closed result member⟩), receipt.meaning, receipt.warm⟩
  intro extra
  simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
    done_stable (fuel + 1) extra _ _ after values receipt.done

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    ∃ fuel values after, execute (fuel + 1) (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial finalCache⟩ : Checked width) = .done values after ∧
      pairs.length = values.length ∧ SourceCurrentAllocatedNativeScopeCache.Scoped after.native := by
  obtain ⟨inputs, fuel, values, after, receipt⟩ := SourceCurrentAllocatedNativeConstructedHistory.query_complete
    history initialValid expression covered value heap built formulas solver pairs available closed ranges
  exact ⟨fuel, values, after, receipt.done, receipt.meaning.length_eq, receipt.scopedCache⟩

end MicroCFTA.OriginalEntryKernelProbe
#print axioms MicroCFTA.OriginalEntryKernelProbe.prepared_actual_complete
