import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionSharedWorkerMemos
import MicroCFTA.SourceCurrentConjunctionSharedWorkerMemoSoundness
import MicroCFTA.SourceCurrentConjunctionSharedWorkerProbes

/-!
# Full outer postconditions for successful shared calls

Current caller inputs derive the ordered global memo bundle, conservative
answer, and full outer postcondition at the same actual returned heap.
The receipt retains the shared worker's full private snapshot. Native
allowances remain explicit. This companion does not change caller selection
or certify the global memo bundle of a failed terminal projection.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionCaller
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "call" => SourceCurrentConjunctionSharedWorker.call
local notation "CallReads" => SourceCurrentConjunctionSharedWorkerMemos.CallReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The actual successful shared call derives its full caller and ordered reads. -/
theorem actual {inventory : Inventory} {p h budget : Nat} {before : Caller width}
    {after : WorkState} {query : Node} {answer : Bool} {saved : Memo} {memos : Memos}
    (completed : call p h budget before.fourth query (physical before.checked) = .done (answer, saved) after)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) completed memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked after.storage.requirements.physical) saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have rawEffects := SourceCurrentConjunctionSharedWorkerEffects.call_effects p h budget before.fourth query
    (physical before.checked) ready available
  have stepEffects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      after.storage.requirements.physical := by
    simpa only [completed, SourceCurrentConjunctionSharedWorker.Outcome.state] using rawEffects.1
  obtain ⟨correct, sound, retained⟩ := SourceCurrentConjunctionSharedWorkerMemoSoundness.call_sound
    formulas solver completed ready available initial.correct
  obtain ⟨final, reads, globals, unfolding, sameQuery⟩ := SourceCurrentConjunctionSharedWorkerMemos.call_memos
    completed ready available memos initial.globals
  have probeEffect := SourceCurrentConjunctionSharedWorkerProbes.call_probes p h budget before.fourth query
    (physical before.checked) ready initial.probes available
  have probes : InternedFreshOrdinaryProbeHeap.Heap after.storage.requirements.physical.heap := by
    simpa only [completed, SourceCurrentConjunctionSharedWorker.Outcome.state] using probeEffect
  have receipt := SourceCurrentAllocatedConjunctionMemo.lift_effects before.checked
    after.storage.requirements.physical initial.ready.good initial.ready.idle stepEffects
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (physical (advancePhysical before.checked after.storage.requirements.physical)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using receipt.effects
  refine ⟨final, reads, ⟨⟨SourceCurrentConjunctionClassScan.advance_ready before.checked
    after.storage.requirements.physical initial.ready receipt.effects,
    initial.admitted.advance _ receipt.extension,
    initial.sound.advance formulas solver _ saved before.merge effects,
    initial.stored.grows receipt.effects.keeps, initial.covered, correct, globals, probes⟩,
    effects, Cache.extends_refl _, retained⟩, sound,
    receipt.effects.keeps.available _ available, unfolding, sameQuery⟩

/-- Current caller entry certifies every successful result of the literal shared call. -/
theorem verified {inventory : Inventory} (p h budget : Nat) (before : Caller width)
    (query : Node) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    match reached : call p h budget before.fourth query (physical before.checked) with
    | .failed _ _ => True
    | .done result after =>
      ∃ final, CallReads p h budget before.fourth query (physical before.checked) reached memos final ∧
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before
            (advancePhysical before.checked after.storage.requirements.physical) result.2 before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1 ∧
        Available after.storage.requirements.physical.heap query ∧
        Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  split
  · trivial
  · rename_i result after reached
    rcases result with ⟨answer, saved⟩
    exact actual formulas solver reached initial available

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionCaller
