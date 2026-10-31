import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionWorkerWarmEffects

set_option autoImplicit false
open scoped Classical

/-! Table meaning at the actual returned conjunction caller. -/
namespace MicroCFTA.SourceCurrentConjunctionCallTableSound
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual call retains both caller result-table laws at its returned checked heap. -/
theorem call_sound {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    SourceCurrentAllocatedPartialMemoSound.Sound formulas solver
      (SourceCurrentAllocatedPartialState.advance before actual.state actual.memo before.merge) := by
  let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked context.ready.good
    context.ready.semantic context.ready.costs
  have produced :=
    SourceCurrentConjunctionWorkerWarmEffects.allocated_call_effects p h budget before.fourth query
      before.checked ready available closed
  have effects : SourceCurrentConjunctionRowsAllocation.Effects
      (physical before.checked) (physical actual.state) := by
    refine Eq.mp ?_ produced
    dsimp only [actual]
    congr; exact Subsingleton.elim _ _
  exact SourceCurrentAllocatedPartialMemoSound.Sound.advance formulas solver context.sound
    actual.state actual.memo before.merge effects

end MicroCFTA.SourceCurrentConjunctionCallTableSound
