import MicroCFTA.SourceCurrentConjunctionWorkerEffects
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.InternedFreshOrdinaryUnfoldMemo
import MicroCFTA.SourceEndpointMemo

set_option autoImplicit false
open scoped Classical

/-!
# Global memo validity at actual current-call endpoints

Actual heap growth retains the same unfolding and query memos. The original
Context supplies constructor validity. The actual call supplies both histories.
-/
namespace MicroCFTA.SourceCurrentConjunctionCallGlobals
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Context" => SourceCurrentAllocatedPartialInvariant.Context

/-- Every actual call outcome retains validity of the same global memo families. -/
theorem call_globals {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width)
    (memos : EndpointMemoGateTrace.Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    EndpointMemoGateTrace.Valid actual.state.native.machine.heap memos := by
  have effects := SourceCurrentConjunctionWorkerEffects.allocated_call_effects
    p h budget before.fourth query before.checked context.ready.semantic.ready.semantic
      context.ready.semantic.ready.covered available closed
  refine ⟨?_, ?_⟩
  · exact InternedFreshOrdinaryUnfoldMemo.grows _ _
      context.ready.semantic.ready.semantic.1.normal.facts.coherent.valid
      effects.2.2.1 effects.2.2.2 _ context.globals.unfolding
  · exact SourceEndpointMemo.grows _ _ effects.2.2.1 effects.2.2.2 _ context.globals.query

end MicroCFTA.SourceCurrentConjunctionCallGlobals
