import MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome

/-!
# Logical completion of the checked shared caller

Current Context and query availability derive sufficient observation
bounds. One actual call supplies its ordered reads and full Post at those
bounds. Larger observations retain all four returned components.
This law requires no numeric profile or additional heap annotation.
Native capacity and complete source enumeration remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionCaller
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedSharedConjunctionWorker
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Current caller facts derive a stable checked success and the literal base receipt without a resource premise. -/
theorem finite {inventory : Inventory} {before : Caller width} {query : Node} {memos : Memos}
    (budget : Nat) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ (answer : Bool) (after : Checked width) (saved : Memo) (snapshot : Snapshot)
      (final : Memos) (p h : Nat),
      call p h budget query before.checked before.fourth = .done answer after saved snapshot ∧
      CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (∀ P H, p ≤ P → h ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨p, h, answer, saved, snapshot, stable⟩ :=
    SourceCurrentConjunctionSharedWorkerCompletion.call_initial budget before.fourth query
      (physical before.checked) ready available
  have raw := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have checked := call_lift (before := before.checked) raw
  have received := SourceCurrentAllocatedSharedConjunctionOutcome.verified formulas solver
    p h budget before query memos initial available
  dsimp only at received
  rw [raw] at received
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state,
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo] at received
  obtain ⟨final, reads, post, resident, retained, same, sound⟩ := received
  refine ⟨answer, advancePhysical before.checked snapshot.storage.requirements.physical,
    saved, snapshot, final, p, h, checked, reads, post, sound, ?_, retained, same, ?_⟩
  · change Available (physical (advancePhysical before.checked snapshot.storage.requirements.physical)).heap query
    rw [SourceCurrentAllocatedQueryMemo.physical_advance]
    exact resident
  · intro P H enoughP enoughH
    exact call_lift (stable P H enoughP enoughH)

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionCaller
