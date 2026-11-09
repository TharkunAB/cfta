import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionSharedWorkerOutcomeMemos
import MicroCFTA.SourceCurrentConjunctionSharedWorkerProbes

/-!
# Full outer postconditions at every shared call outcome

Current caller inputs derive ordered global memos and the full Post at the
actual returned heap, including failed prefixes. A failed call retains the
incoming fourth memo. Its original diagnostic and full private snapshot
remain in the unchanged worker outcome. This proof does not select a caller
adapter or identify the old eager failure interface with the shared one.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads returnedMemo)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "call" => SourceCurrentConjunctionSharedWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem lift_post {inventory : Inventory} {before : Caller width} {after : Physical}
    {saved : Memo} {memos final : Memos} (initial : Context formulas solver inventory before memos)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) after)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved)
    (retained : SourceCurrentEmptinessMemo.Extends before.fourth saved)
    (globals : EndpointMemoGateTrace.Valid after.heap final)
    (probes : InternedFreshOrdinaryProbeHeap.Heap after.heap) :
    Post formulas solver inventory before
      (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) saved before.merge) final := by
  have receipt := SourceCurrentAllocatedConjunctionMemo.lift_effects before.checked after
    initial.ready.good initial.ready.idle effects
  have lifted : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (physical (advancePhysical before.checked after)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using receipt.effects
  exact ⟨⟨SourceCurrentConjunctionClassScan.advance_ready before.checked after initial.ready receipt.effects,
    initial.admitted.advance after receipt.extension,
    initial.sound.advance formulas solver _ saved before.merge lifted,
    initial.stored.grows receipt.effects.keeps, initial.covered, correct, globals, probes⟩,
    lifted, Cache.extends_refl _, retained⟩

/-- Current caller entry derives a full Post and ordered bundle on every actual outcome. -/
theorem verified {inventory : Inventory} (p h budget : Nat) (before : Caller width)
    (query : Node) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    let outcome := call p h budget before.fourth query (physical before.checked)
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked outcome.state.storage.requirements.physical)
          (returnedMemo before.fourth outcome) before.merge) final ∧
      Available outcome.state.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (match outcome with
       | .failed _ _ => True
       | .done result _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1) := by
  dsimp only
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have effects := (SourceCurrentConjunctionSharedWorkerEffects.call_effects p h budget before.fourth query
    (physical before.checked) ready available).1
  have probes := SourceCurrentConjunctionSharedWorkerProbes.call_probes p h budget before.fourth query
    (physical before.checked) ready initial.probes available
  obtain ⟨final, reads, globals, retained, same⟩ := SourceCurrentConjunctionSharedWorkerOutcomeMemos.call_memos
    p h budget before.fourth query (physical before.checked) ready available memos initial.globals
  obtain ⟨correct, fourthRetained, sound⟩ := SourceCurrentConjunctionSharedWorkerOutcomeMemos.call_fourth
    formulas solver p h budget before.fourth query (physical before.checked) ready available initial.correct
  exact ⟨final, reads, lift_post formulas solver initial effects correct fourthRetained globals probes,
    effects.keeps.available query available, retained, same, sound⟩

/-- A failed prefix retains its exact heap, all caller invariants, and the incoming fourth memo. -/
theorem failed {inventory : Inventory} {p h budget : Nat} {before : Caller width}
    {query : Node} {memos : Memos} {after : WorkState}
    {fault : SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula}
    (actual : call p h budget before.fourth query (physical before.checked) = .failed fault after)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked after.storage.requirements.physical) before.fourth before.merge) final ∧
      Available after.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have complete := verified formulas solver p h budget before query memos initial available
  dsimp only at complete
  rw [actual] at complete
  obtain ⟨final, reads, post, resident, retained, same, _⟩ := complete
  exact ⟨final, reads, post, resident, retained, same⟩

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
