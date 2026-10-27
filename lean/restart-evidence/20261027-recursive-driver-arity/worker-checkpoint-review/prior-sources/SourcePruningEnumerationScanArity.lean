import MicroCFTA.SourceCurrentConjunctionClassScanCompletion
import MicroCFTA.SourcePruningEnumerationGateArity
import MicroCFTA.SourcePruningEnumerationSeededArity
import MicroCFTA.SourcePruningEnumerationConjunctionArity

/-!
# Arity through the actual current class scan

Both gates retain the invariant at their real returned heaps.
Reached ranges derive the seeded query and its actual physical state.
The current memo call starts at that state.
-/
namespace MicroCFTA.SourcePruningEnumerationScanArity
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

private theorem query_heap_effects
    (unconstrained : Value Symbol Guard → Bool)
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) query middle)
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) answer after saved)
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor))
    (proper : ∀ path ∈ paths, path ≠ []) (ready : Ready before)
    (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) :
    Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧ Heap after.heap := by
  have initialReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate initialReady available
  have advanced := advance_ready before ⟨anchor, before.operations⟩ ready first.1
  have anchorHeap := (SourcePruningEnumerationGateArity.Secondary.class_effects unconstrained gate
    ready.semantic ready.costs available heap).2.2.2
  have queryHeap := SourcePruningEnumerationSeededArity.seeded_heap unconstrained anchor anchorSemantic anchorReady
    seeded ranges advanced.good first.1.ready advanced.scopedCache advanced.idle anchorValues (grows_refl anchor)
    (by
      intro path member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact supported original present) anchorHeap
  obtain ⟨chosen, reached, completed, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
    SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values gate ready.good initialReady
      ready.scopedCache ready.idle available proper ranges
  obtain ⟨rfl, rfl⟩ := seeded.unique completed
  have queryReady : Ready middle :=
    ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
  have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
  obtain ⟨finalReady, callEffects, finalCorrect, _, _⟩ :=
    memo_effects formulas solver call queryReady queryAvailable queryCorrect
  have afterHeap := SourcePruningEnumerationConjunctionArity.call_heap call queryEffects.ready queryAvailable queryHeap
  exact ⟨finalReady, queryEffects.trans callEffects,
    fun value member => callEffects.keeps.available value (queryEffects.keeps.available value (available value member)),
    finalCorrect, afterHeap⟩

/-- The actual class scan retains arity under its original reached-range and physical contracts. -/
theorem scan_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  revert ready available proper correct ranges heap
  induction actual with
  | nil => intro _ _ _ _ _ heap; exact heap
  | selected primary rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePruningEnumerationGateArity.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      exact ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) (ranges.1 _ primary) current
  | skipped primary secondary rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePruningEnumerationGateArity.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      have later := (SourcePruningEnumerationGateArity.Secondary.class_effects unconstrained secondary
        first.1.semantic first.1.costs first.2.2 current).2.2.2
      exact ih second.1 second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver (first.2.1.trans second.2.1).keeps _ correct)
        (ranges.2.1 _ primary _ secondary) later
  | continued primary secondary seeded call rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePruningEnumerationGateArity.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      have reached := ranges.2.2 _ primary _ secondary
      obtain ⟨nextReady, _effects, nextValues, nextCorrect, nextHeap⟩ := query_heap_effects unconstrained
        secondary seeded call reached.1 (proper _ List.mem_cons_self) first.1 first.2.2 formulas solver
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) current
      exact ih nextReady nextValues (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        nextCorrect (reached.2 _ _ seeded _ _ call) nextHeap
  | stopped primary secondary seeded call =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePruningEnumerationGateArity.Primary.class_effects unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      exact (query_heap_effects unconstrained secondary seeded call (ranges.2.2 _ primary _ secondary).1
        (proper _ List.mem_cons_self) first.1 first.2.2 formulas solver
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) current).2.2.2.2

end MicroCFTA.SourcePruningEnumerationScanArity
