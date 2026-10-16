import MicroCFTA.SourceCurrentAllocatedNativeColdHistoryExact

open MicroCFTA
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard

#check SourceCurrentAllocatedNativeColdHistoryExact.cold_complete
#print axioms SourceCurrentAllocatedNativeColdHistoryExact.cold_complete

namespace MicroCFTA.ColdHistoryKernelProbe
variable {width : Nat}

theorem actual_serial_cold_history [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width)) (semantic : SemanticReady machine.heap)
    (pairs : List Query) (originals : ∀ value ∈ SourceCurrentAllocatedNativeColdHistoryExact.operands pairs, Original value)
    (available : Values machine.heap (SourceCurrentAllocatedNativeColdHistoryExact.operands pairs))
    (closed : ∀ value ∈ SourceCurrentAllocatedNativeColdHistoryExact.operands pairs, value.free = [])
    (ranges : WordRanges (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ fuel values after,
      execute (fuel + 1) (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
        (⟨initial width machine, operations⟩ : Checked width) = .done values after ∧
      (∀ extra, execute (fuel + extra + 1) (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
        (⟨initial width machine, operations⟩ : Checked width) = .done values after) ∧
      Good after ∧ SemanticReady after.native.machine.heap ∧ SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧
      (∀ value ∈ values, Available after.native.machine.heap value ∧ value.free = []) ∧
      All₂ (fun pair value => ∀ output term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.1 term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.2 term) pairs values ∧
      All₂ (fun pair value => ∀ key,
        SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key →
          execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2)) after = .done value after) pairs values := by
  obtain ⟨fuel, values, after, receipt⟩ := SourceCurrentAllocatedNativeColdHistoryExact.cold_complete
    formulas solver machine operations valid semantic pairs originals available closed ranges
  refine ⟨fuel, values, after, receipt.done, ?_, receipt.good, receipt.semantic, receipt.scopedCache, receipt.idle,
    (fun value member => ⟨receipt.result value member, receipt.closed value member⟩), receipt.meaning, receipt.warm⟩
  intro extra
  simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
    done_stable (fuel + 1) extra _ (⟨initial width machine, operations⟩ : Checked width) after values receipt.done

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))}
    {fuel : Nat} {pairs : List Query} {before after : Checked width} {values : List (Value Symbol Guard)}
    (receipt : SourceCurrentAllocatedNativeWarmHistory.Receipt source formulas solver inputs fuel pairs before values after) :
    pairs.length = values.length := receipt.meaning.length_eq

end MicroCFTA.ColdHistoryKernelProbe
#print axioms MicroCFTA.ColdHistoryKernelProbe.actual_serial_cold_history
