import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorkerGuardArity
import MicroCFTA.SourceCurrentAllocatedConjunctionMemo
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame

/-!
# Native query Frames through actual checked shared calls

A completed checked call retains its literal physical endpoint. Current
effects and the existing causal guard heap preserve the same native query
Frame. The proof supplies no future graph, guard heap or closure premise.
-/
namespace MicroCFTA.SourceCurrentSharedConjunctionCallerNumeric
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- A literal shared checked success retains every native Frame field at its exact returned state. -/
theorem of_call (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {p h budget : Nat} {before after : Checked width}
    {memo saved : Memo} {query : Node} {answer : Bool} {snapshot : Snapshot}
    (actual : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget query before memo =
      .done answer after saved snapshot)
    (frame : Frame formulas solver inventory before)
    (available : Available before.native.machine.heap query) :
    Frame formulas solver inventory after := by
  obtain ⟨raw, advanced⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done actual
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good
    frame.ready.semantic frame.ready.costs
  have effects := (SourceCurrentConjunctionSharedWorkerEffects.call_effects
    p h budget memo query (physical before) ready available).1
  have guards := SourceCurrentConjunctionSharedWorkerGuardArity.call_guard_heap Plain
    p h budget memo query (physical before) ready frame.context.guards available
  rw [raw] at effects guards
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at effects guards
  have returnedGuards : SourceCurrentConstrainedCapGuardHeap.Heap Plain
      (advancePhysical before snapshot.storage.requirements.physical).native.machine.heap := by
    change SourceCurrentConstrainedCapGuardHeap.Heap Plain
      (physical (advancePhysical before snapshot.storage.requirements.physical)).heap
    rw [SourceCurrentAllocatedQueryMemo.physical_advance]
    exact guards
  have tables := SourceCurrentAllocatedQueryMemo.advance_tables before snapshot.storage.requirements.physical
  rw [advanced]
  exact SourceCurrentConstrainedCapOperandFrame.advance frame
    (SourceCurrentConjunctionClassScan.advance_ready before snapshot.storage.requirements.physical frame.ready effects)
    (SourceCurrentAllocatedQueryMemo.advance_extension before snapshot.storage.requirements.physical effects)
    tables.1 tables.2.1 returnedGuards

end MicroCFTA.SourceCurrentSharedConjunctionCallerNumeric
