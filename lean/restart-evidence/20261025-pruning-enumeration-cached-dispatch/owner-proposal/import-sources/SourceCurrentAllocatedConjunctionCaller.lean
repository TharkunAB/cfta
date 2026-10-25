import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
import MicroCFTA.SourceCurrentAllocatedProbeConjunction

/-!
# Current conjunction calls retain the full outer caller

The supplied call and its own read receipt derive the same returned caller.
Both outer result families, the warm merge table, native cells, and input
inventory remain. The fourth memo receives only the completed answer.
Global read receipts remain logical evidence rather than host event replay.
-/
namespace MicroCFTA.SourceCurrentAllocatedConjunctionCaller
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Call" => SourceCurrentConjunctionMemo.Call
local notation "CallReads" => SourceCurrentConjunctionGlobalMemos.CallReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The supplied reads derive the full returned caller and the one-sided emptiness answer. -/
theorem verified {inventory : Inventory} {budget : Nat} {before : Caller width} {after : Physical}
    {query : Value Symbol Guard} {answer : Bool} {saved : Memo} {memos final : Memos}
    {actual : Call budget before.fourth query (physical before.checked) answer after saved}
    (reads : CallReads actual memos final) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ Available after.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨receipt, correct, sound, retained⟩ := SourceCurrentAllocatedConjunctionMemo.call_effects formulas solver
    actual initial.ready.good initial.ready.semantic initial.ready.costs initial.ready.idle available initial.correct
  have globals := SourceCurrentAllocatedConjunctionReadValidity.call reads ready available initial.globals
  have probes := SourceCurrentAllocatedProbeConjunction.call_heap actual ready available initial.probes
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (physical (advancePhysical before.checked after)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using receipt.effects
  refine ⟨⟨⟨SourceCurrentConjunctionClassScan.advance_ready before.checked after initial.ready receipt.effects,
    initial.admitted.advance after receipt.extension,
    initial.sound.advance formulas solver _ saved before.merge effects,
    initial.stored.grows receipt.effects.keeps, initial.covered, correct, globals.1, probes⟩,
    effects, Cache.extends_refl _, retained⟩, sound, receipt.effects.keeps.available _ available,
    globals.2.1, globals.2.2⟩

/-- Initial caller facts construct reads for the same completed physical call. -/
theorem actual {inventory : Inventory} {budget : Nat} {before : Caller width} {after : Physical}
    {query : Value Symbol Guard} {answer : Bool} {saved : Memo} {memos : Memos}
    (call : Call budget before.fourth query (physical before.checked) answer after saved)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ final, CallReads call memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ Available after.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨final, reads, _⟩ := SourceCurrentConjunctionGlobalMemos.call_memos call ready available memos initial.globals
  exact ⟨final, reads, verified formulas solver reads initial available⟩

/-- Legitimate caller entry constructs a finite current call and its full returned invariant. -/
theorem finite {inventory : Inventory} {before : Caller width} {query : Value Symbol Guard} {memos : Memos}
    (budget : Nat) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer after saved final, ∃ call : Call budget before.fourth query (physical before.checked) answer after saved,
      CallReads call memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ Available after.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨answer, after, saved, call, _⟩ := SourceCurrentConjunctionMemo.complete budget before.fourth query
    (physical before.checked) ready available
  obtain ⟨final, reads, post⟩ := actual formulas solver call initial available
  exact ⟨answer, after, saved, final, call, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedConjunctionCaller
