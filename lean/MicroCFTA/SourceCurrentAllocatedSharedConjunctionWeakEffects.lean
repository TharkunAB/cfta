import MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
import MicroCFTA.SourceCurrentConjunctionSharedWorkerWeakEffects

/-!
# Weak shared effects at the checked and outer caller boundaries

The actual shared endpoint advances the existing checked state. Both caller
boundaries retain semantic validity, coverage, growth and issued identities
from the original weak premises. These laws neither select an adapter nor
certify Boolean answers without the stronger current caller invariants.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionWeakEffects
open Cache
open InternedConstructorTemplates (Value EdgeKey Grows grows_refl)
open InternedRecordCoherence (Covered)
open InternedProbeProvenance (Available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (returnedMemo)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "call" => SourceCurrentConjunctionSharedWorker.call
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))] {width : Nat}

/-- The literal checked advance retains both existing callers' original weak contract. -/
theorem checked_effects (p h budget : Nat) (memo : Memo) (query : Node) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap) (covered : Covered [] before.native.machine.heap)
    (available : Available before.native.machine.heap query) (closed : query.free = []) :
    let actual := call p h budget memo query (physical before)
    let after := advancePhysical before actual.state.storage.requirements.physical
    SemanticHeap after.native.machine.heap ∧ Covered [] after.native.machine.heap ∧
      Grows before.native.machine.heap after.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued after.native.machine.heap.nodes.issued := by
  exact SourceCurrentConjunctionSharedWorkerWeakEffects.call_effects
    p h budget memo query (physical before) semantic covered available closed

/-- The same outer caller update retains weak effects on successful and failed outcomes. -/
theorem caller_effects (p h budget : Nat) (query : Node) (before : Caller width)
    (semantic : SemanticHeap before.checked.native.machine.heap)
    (covered : Covered [] before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := call p h budget before.fourth query (physical before.checked)
    let after := SourceCurrentAllocatedPartialState.advance before
      (advancePhysical before.checked actual.state.storage.requirements.physical)
      (returnedMemo before.fourth actual) before.merge
    SemanticHeap after.checked.native.machine.heap ∧ Covered [] after.checked.native.machine.heap ∧
      Grows before.checked.native.machine.heap after.checked.native.machine.heap ∧
      Extends before.checked.native.machine.heap.nodes.issued after.checked.native.machine.heap.nodes.issued := by
  exact checked_effects p h budget before.fourth query before.checked semantic covered available closed

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionWeakEffects
