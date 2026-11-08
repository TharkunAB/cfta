import MicroCFTA.SourceCurrentConjunctionProbeBirthCore
import MicroCFTA.SourcePruningTemplates
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

set_option autoImplicit false
open scoped Classical

/-!
# Current caller inputs for stored-unfold probe births

The caller Context supplies the generic unfolding law's initial facts.
The imported generic law retains its existing public qualified name.
-/
namespace MicroCFTA.SourceCurrentConjunctionProbeBirth
open InternedConstructorTemplates InternedProbeProvenance

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- The original current context supplies every input to the actual cold-unfold probe law. -/
theorem current_unfold_heap {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (value : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap value) :
    InternedFreshOrdinaryProbeHeap.Heap
      (InternedFreshOrdinaryStoredSubstitution.unfold value before.checked.native.machine.heap).state :=
  unfold_heap value before.checked.native.machine.heap context.ready.semantic.ready.semantic.1
    context.probes available

end MicroCFTA.SourceCurrentConjunctionProbeBirth
