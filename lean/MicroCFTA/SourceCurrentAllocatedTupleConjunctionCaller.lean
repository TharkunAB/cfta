import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedTupleConjunctionReadValidity
import MicroCFTA.SourceCurrentConjunctionDemandMemo
import MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects

/-!
# Tuple-budget calls retain the full outer caller

The actual call and its supplied reads retain the shared caller invariant.
Both outer result families, warm merge entries, native tables, domains, and
input inventory remain. Probe preservation follows the same call's stable
replay. Logical reads do not establish native lazy demand or publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedTupleConjunctionCaller
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
local notation "Call" => SourceCurrentConjunctionDemandWorklistExecution.Call
local notation "CallReads" => SourceCurrentConjunctionDemandWorklistMemos.CallReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

private theorem call_probes {budget : Nat} {memo saved : Memo} {query : Value Symbol Guard}
    {before after : Physical} {answer : Bool} (actual : Call budget memo query before answer after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.heap) : InternedFreshOrdinaryProbeHeap.Heap after.heap := by
  obtain ⟨p, h, done⟩ := SourceCurrentConjunctionDemandWorklistExecution.call_complete actual
  have kept : InternedFreshOrdinaryProbeHeap.Heap
      (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state.heap :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _)
      (SourceCurrentConjunctionDemandWorklistEffects.call_probes p h budget memo query before ready probes available)
  have completed := done p h (Nat.le_refl _) (Nat.le_refl _)
  simpa only [completed, SourceCurrentConjunctionWorker.Outcome.state] using kept

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Supplied tuple-call reads derive the same full returned caller and conservative answer. -/
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
  obtain ⟨stepEffects, correct, sound, retained⟩ := SourceCurrentConjunctionDemandMemo.verified formulas solver
    actual ready available initial.correct
  have receipt := SourceCurrentAllocatedConjunctionMemo.lift_effects before.checked after
    initial.ready.good initial.ready.idle stepEffects
  have globals := SourceCurrentAllocatedTupleConjunctionReadValidity.call reads ready available initial.globals
  have probes := call_probes actual ready available initial.probes
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (physical (advancePhysical before.checked after)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using receipt.effects
  refine ⟨⟨⟨SourceCurrentConjunctionClassScan.advance_ready before.checked after initial.ready receipt.effects,
    initial.admitted.advance after receipt.extension,
    initial.sound.advance formulas solver _ saved before.merge effects,
    initial.stored.grows receipt.effects.keeps, initial.covered, correct, globals.1, probes⟩,
    effects, Cache.extends_refl _, retained⟩, sound, receipt.effects.keeps.available _ available,
    globals.2.1, globals.2.2⟩

/-- Initial caller facts derive reads for the same completed tuple call. -/
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
  obtain ⟨final, reads, _⟩ := SourceCurrentConjunctionDemandWorklistMemos.call_memos call ready available memos initial.globals
  exact ⟨final, reads, verified formulas solver reads initial available⟩

/-- Legitimate caller entry derives a finite tuple call and its full returned invariant. -/
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
  obtain ⟨answer, after, saved, call, _⟩ := SourceCurrentConjunctionDemandMemo.complete budget before.fourth query
    (physical before.checked) ready available
  obtain ⟨final, reads, post⟩ := actual formulas solver call initial available
  exact ⟨answer, after, saved, final, call, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedTupleConjunctionCaller
