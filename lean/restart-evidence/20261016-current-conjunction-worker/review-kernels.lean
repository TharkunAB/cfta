import MicroCFTA.SourceCurrentAllocatedConjunctionWorker
import MicroCFTA.SourceCurrentAllocatedConjunctionCaller

namespace MicroCFTA.CurrentConjunctionCallerIndependentReview
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem fourth_hit_precedes_the_open_guard_at_zero_read_bounds
    (budget : Nat) (query original : Value Symbol Guard) (answer : Bool)
    (before : Checked width) (memo : Memo)
    (hit : memo query.referenceOf = some (original, answer)) :
    SourceCurrentAllocatedConjunctionWorker.call 0 0 budget query before memo = .done answer before memo := by
  have raw : SourceCurrentConjunctionWorker.call 0 0 budget memo query (physical before) =
      .done (answer, memo) (physical before) := by
    simp only [SourceCurrentConjunctionWorker.call, hit]
  simpa only [SourceCurrentAllocatedConjunctionMemo.advance_self] using
    SourceCurrentAllocatedConjunctionWorker.call_lift raw

theorem open_miss_inserts_false_without_changing_checked_state
    (p h budget : Nat) (query : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (absent : memo query.referenceOf = none)
    (openQuery : SourceCurrentConjunctionWorklist.closed query = false) :
    SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo =
      .done false before (SourceCurrentEmptinessMemo.insert memo query false) := by
  have raw : SourceCurrentConjunctionWorker.call p h budget memo query (physical before) =
      .done (false, SourceCurrentEmptinessMemo.insert memo query false) (physical before) := by
    simp only [SourceCurrentConjunctionWorker.call, absent, SourceCurrentConjunctionWorker.decision,
      openQuery, Bool.false_eq_true, ite_false, SourceCurrentConjunctionWorker.Outcome.bind]
  simpa only [SourceCurrentAllocatedConjunctionMemo.advance_self] using
    SourceCurrentAllocatedConjunctionWorker.call_lift raw

theorem physical_failure_retains_native_tables_and_initial_fourth_memo
    (p h budget : Nat) (query : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (fault : SourceCurrentConjunctionWorker.Fault Symbol FullSyntax.Formula) (after : Physical)
    (failed : SourceCurrentConjunctionWorker.call p h budget memo query (physical before) = .failed fault after) :
    SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo =
      .failed fault (advancePhysical before after) memo ∧
      (advancePhysical before after).operations = after.equality ∧
      (advancePhysical before after).native.nodes = before.native.nodes ∧
      (advancePhysical before after).native.edges = before.native.edges ∧
      (advancePhysical before after).native.machine.domains = before.native.machine.domains := by
  obtain ⟨nodes, edges, domains⟩ := SourceCurrentAllocatedQueryMemo.advance_tables before after
  exact ⟨SourceCurrentAllocatedConjunctionWorker.call_failed_lift failed, rfl, nodes, edges, domains⟩

theorem supplied_read_validity_retains_same_inventory_and_true_soundness
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory) (budget : Nat)
    (before : Caller width) (after : Physical) (query : Value Symbol Guard) (saved : Memo) (memos final : Memos)
    (actual : SourceCurrentConjunctionMemo.Call budget before.fourth query (physical before.checked) true after saved)
    (reads : SourceCurrentConjunctionGlobalMemos.CallReads actual memos final)
    (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    let returned := SourceCurrentAllocatedPartialState.advance before
      (advancePhysical before.checked after) saved before.merge
    SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory returned.checked ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      EndpointMemoGateTrace.Valid after.heap final ∧
      SourceCurrentEmptinessMemo.Extends before.fourth saved ∧
      final.query = memos.query ∧
      (∀ ambient term, ¬InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term) := by
  obtain ⟨post, sound, _, _, unchanged⟩ :=
    SourceCurrentAllocatedConjunctionCaller.verified formulas solver reads initial available
  exact ⟨post.context.admitted, post.context.correct, post.context.globals,
    post.fourthRetained, unchanged, sound.2 rfl⟩

end MicroCFTA.CurrentConjunctionCallerIndependentReview
