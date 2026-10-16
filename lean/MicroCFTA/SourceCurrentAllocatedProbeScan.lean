import MicroCFTA.SourceCurrentAllocatedProbeQuery

/-!
# Filtered probes through the current ordered class scan

Only reached original classes execute. The proof follows primary and
secondary short circuits, the actual seeded query, and the current memo
call. No probe obligation is supplied for an unvisited suffix.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeScan
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan
open InternedFreshOrdinaryProbeHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Every actual reached scan derives its final probe heap from the initial heap. -/
theorem scan_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo)
    (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  induction actual generalizing inventory with
  | nil => exact probes
  | @selected paths heap classes before memo outcome selected after saved primary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have afterProbes := (SourceCurrentAllocatedProbeGates.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available probes).2.2.2
      exact ih inventory first.1
        (admitted.advance ⟨heap, before.operations⟩ (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1))
        first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct)
        (ranges.1 heap primary) afterProbes
  | @skipped paths heap anchor classes before memo outcome selected after saved primary secondary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      have firstProbes := (SourceCurrentAllocatedProbeGates.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available probes).2.2.2
      have secondProbes := (SourceCurrentAllocatedProbeGates.Secondary.class_effects unconstrained secondary
        first.1.semantic first.1.costs first.2.2 firstProbes).2.2.2
      exact ih inventory second.1
        (firstAdmission.advance ⟨anchor, (advanceHeap before heap).operations⟩
          (SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1))
        second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver second.2.1.keeps memo firstCorrect)
        (ranges.2.1 heap primary anchor secondary) secondProbes
  | @continued paths heap anchor before query middle memo later savedMemo classes outcome selected after saved
      primary secondary seeded decision rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have reached := ranges.2.2 heap primary anchor secondary
      obtain ⟨next, queryReceipt, _⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
        formulas solver inventory unconstrained paths values secondary seeded first.1.good first.2.1.ready
        first.1.scopedCache first.1.idle firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1
      have queryReady : Ready middle := ⟨queryReceipt.good, queryReceipt.effects.ready.semantic,
        queryReceipt.effects.ready.costs, queryReceipt.scopes, queryReceipt.idle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryReceipt.effects.keeps memo firstCorrect
      obtain ⟨memoReady, memoEffects, memoCorrect, _, _⟩ :=
        memo_effects formulas solver decision queryReady queryReceipt.available queryCorrect
      have firstProbes := (SourceCurrentAllocatedProbeGates.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available probes).2.2.2
      have queryProbes := SourceCurrentAllocatedProbeQuery.false_class_heap formulas solver inventory unconstrained
        secondary seeded first.1 firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1 firstProbes
      have memoProbes := SourceCurrentAllocatedProbeConjunction.call_heap decision queryReceipt.effects.ready queryReceipt.available queryProbes
      exact ih next memoReady
        (queryReceipt.admitted.advance later (SourceCurrentAllocatedQueryMemo.advance_extension middle later memoEffects))
        (fun value member => memoEffects.keeps.available value (queryReceipt.effects.keeps.available value (first.2.2 value member)))
        (fun paths member => proper paths (List.mem_cons_of_mem _ member)) memoCorrect
        (reached.2 query middle seeded later savedMemo decision) memoProbes
  | @stopped paths heap anchor before query middle memo later saved classes primary secondary seeded decision =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have reached := ranges.2.2 heap primary anchor secondary
      obtain ⟨_, queryReceipt, _⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
        formulas solver inventory unconstrained paths values secondary seeded first.1.good first.2.1.ready
        first.1.scopedCache first.1.idle firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1
      have firstProbes := (SourceCurrentAllocatedProbeGates.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available probes).2.2.2
      have queryProbes := SourceCurrentAllocatedProbeQuery.false_class_heap formulas solver inventory unconstrained
        secondary seeded first.1 firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1 firstProbes
      exact SourceCurrentAllocatedProbeConjunction.call_heap decision queryReceipt.effects.ready queryReceipt.available queryProbes

end MicroCFTA.SourceCurrentAllocatedProbeScan
