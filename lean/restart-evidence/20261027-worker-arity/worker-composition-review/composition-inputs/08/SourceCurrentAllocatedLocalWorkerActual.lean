import MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentAllocatedLocalReductionActual
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedProbeActual

/-!
# Full caller receipts for literal local equality reduction

The actual stored field and initial caller construct a strict local graph.
Stable execution and unconditional success uniqueness identify its complete
return with any supplied literal success. The same strict reads derive the
final probe heap. The receipt and caller postcondition use the same computed
inventory. Host demand and memo publication remain separate boundaries.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalWorkerActual
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt Ranges)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedLocalWorker (reduce)
open SourceCurrentAllocatedLocalWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

private theorem caller_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory next : Inventory} {original : Guard} {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before : Caller width} {after : Checked width}
    {savedFourth : Fourth} {saved : Memo} {memos final : Memos}
    {actual : Reduction budget loaded inherited values before.checked before.fourth before.merge
      results after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (receipt : Receipt formulas solver next original loaded inherited values results before.checked after
      before.fourth savedFourth before.merge saved final) :
    Post formulas solver next before
      (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  have probes := SourceCurrentAllocatedProbeParent.local_heap formulas solver inventory original reads
    initial.ready initial.admitted cached found inheritedReady available initial.correct initial.stored initial.covered
    (SourceCurrentAllocatedLocalReductionActual.ranges_of_finite ranges) initial.globals initial.probes
  exact ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver after savedFourth saved receipt.effects,
    receipt.stored, receipt.covered, receipt.correct, receipt.globals, probes⟩,
    receipt.effects, receipt.retained, receipt.fourthRetained⟩

/-- A supplied literal success derives its own strict local graph and same returned receipt. -/
theorem sound
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original : Guard} {g s r e p h m c n budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before : Caller width} {after : Checked width} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved) :
    ∃ next final,
      ∃ actual : Reduction budget loaded inherited values before.checked before.fourth before.merge
          results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before.checked after
          before.fourth savedFourth before.merge saved final := by
  obtain ⟨chosen, reached, fourth, memo, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedLocalReductionActual.finite formulas solver inventory budget original loaded inherited
      values before.checked before.fourth before.merge initial.ready initial.admitted cached found inheritedReady
      available initial.correct initial.stored initial.covered ranges memos initial.globals
  obtain ⟨G, S, R, E, P, H, M, C, N, stable⟩ :=
    SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.reduce_done_unique
    (stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨next, final, actual, reads, receipt⟩

/-- A literal success retains the full caller and probe heap at its own computed inventory. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original : Guard} {g s r e p h m c n budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before : Caller width} {after : Checked width} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved) :
    ∃ next final,
      ∃ actual : Reduction budget loaded inherited values before.checked before.fourth before.merge
          results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before.checked after
          before.fourth savedFourth before.merge saved final ∧
        Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨next, final, actual, reads, receipt⟩ :=
    sound formulas solver initial cached found inheritedReady available ranges done
  exact ⟨next, final, actual, reads, receipt,
    caller_post formulas solver reads initial cached found inheritedReady available ranges receipt⟩

/-- Initial same-cache field facts construct stable literal reduction and its full caller return. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (initial : Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge) :
    ∃ results after savedFourth saved next final,
      StableRun (fun g s r e p h m c n =>
        reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge)
        results after savedFourth saved ∧
      ∃ actual : Reduction budget loaded inherited values before.checked before.fourth before.merge
          results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before.checked after
          before.fourth savedFourth before.merge saved final ∧
        Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
  obtain ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedLocalReductionActual.finite formulas solver inventory budget original loaded inherited
      values before.checked before.fourth before.merge initial.ready initial.admitted cached found inheritedReady
      available initial.correct initial.stored initial.covered ranges memos initial.globals
  exact ⟨results, after, savedFourth, saved, next, final,
    SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual, actual, reads, receipt,
    caller_post formulas solver reads initial cached found inheritedReady available ranges receipt⟩

end MicroCFTA.SourceCurrentAllocatedLocalWorkerActual
