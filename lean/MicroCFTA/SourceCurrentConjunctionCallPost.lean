import MicroCFTA.SourceCurrentConjunctionCallClassScanReady
import MicroCFTA.SourceCurrentConjunctionCallTableSound
import MicroCFTA.SourceCurrentConjunctionWorkerProbes
import MicroCFTA.SourceCurrentConjunctionCallSound
import MicroCFTA.SourceCurrentConjunctionCallGlobals

set_option autoImplicit false
open scoped Classical

/-! Complete caller preservation at the actual conjunction-call endpoint. -/
namespace MicroCFTA.SourceCurrentConjunctionCallPost
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual call outcome retains the original inventory, memos and full context. -/
theorem call_post {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    let after := SourceCurrentAllocatedPartialState.advance before actual.state actual.memo before.merge
    SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory before after memos := by
  cases Subsingleton.elim (inferInstance : DecidableEq (EdgeKey Symbol Guard))
    (fun a b => instDecidableEqEdgeKey a b)
  have checked := SourceCurrentConjunctionCallSound.call_correct p h budget query before memos
    context available closed
  have initial := SourceCurrentAllocatedConjunctionMemo.ready before.checked context.ready.good
    context.ready.semantic context.ready.costs
  have effects := SourceCurrentConjunctionWorkerWarmEffects.allocated_call_effects p h budget
    before.fourth query before.checked initial available closed
  exact {
    context := {
      ready := SourceCurrentConjunctionCallClassScanReady.call_ready p h budget query before memos context available closed
      admitted := checked.1.1
      sound := SourceCurrentConjunctionCallTableSound.call_sound p h budget query before memos context available closed
      stored := checked.1.2.1
      covered := context.covered
      correct := checked.2.1
      globals := SourceCurrentConjunctionCallGlobals.call_globals p h budget query before memos context available closed
      probes := SourceCurrentConjunctionWorkerProbes.allocated_call_heap p h budget query before memos context available closed
    }
    effects := effects
    retained := Cache.extends_refl before.merge
    fourthRetained := SourceCurrentConjunctionCallRetained.call_fourth_extends p h budget query before.checked before.fourth
  }

end MicroCFTA.SourceCurrentConjunctionCallPost
