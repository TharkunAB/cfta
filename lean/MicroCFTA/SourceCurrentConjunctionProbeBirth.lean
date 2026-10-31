import MicroCFTA.InternedFreshOrdinaryProbeHeap
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.SourcePruningTemplates
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

set_option autoImplicit false
open scoped Classical

/-!
# Filtered probe births in actual stored unfolding

The actual stored executor uses the source builder. Its initial context and
resident replacements supply that builder's inputs. New nested binders retain
the actual filtered probes. Native query prefixes remain a separate obligation.
-/
namespace MicroCFTA.SourceCurrentConjunctionProbeBirth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)

/-- Actual stored unfolding retains old probes and derives clean probes for new binders. -/
theorem unfold_heap {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    {captures : List (Value Symbol Guard)} (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state captures)
    (probes : InternedFreshOrdinaryProbeHeap.Heap state) (available : Available state value) :
    InternedFreshOrdinaryProbeHeap.Heap
      (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact probes
  | mu entry body depth ordinary =>
    let environment : Environment Symbol Guard := fun name =>
      if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
    have replacements : Replacements state environment := by
      intro name replacement found
      dsimp only [environment] at found
      split at found
      · cases found
        exact available
      · cases found
    have inputs := inputs_available body environment state
      (available.children body (by simp [children])) replacements
    have sourceContext : InternedFreshOrdinaryContext.Context state ((leaves body).map (input environment)) :=
      ⟨context.normal, inputs, context.profiles, context.freeNames⟩
    exact InternedFreshOrdinaryProbeHeap.build_heap (encode (leaves body) [] body)
      ((leaves body).map (input environment)) state sourceContext probes

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
