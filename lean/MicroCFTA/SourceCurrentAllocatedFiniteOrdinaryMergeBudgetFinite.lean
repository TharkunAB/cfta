import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite

/-!
# Constructed ordinary Merge returns with static constructor budgets

Initial profiles bound actual constructor requests through the whole call.
The endpoint constructs its own allocated call and stable literal return.
The trace retains all body work before the actual winner is returned.
Other resource families and host execution remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetFinite
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
open SourceCurrentAllocatedMergeWorkerCompletion (StableCall)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial resident profiles construct a literal return and bound every actual constructor request. -/
theorem finite (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (profiles : Profiles memo)
    (available : Available before.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved requests,
      SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved ∧
      StableCall clear input before memo output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input ∧ Trace before.heap after.heap requests ∧
      nodeRequests requests ≤ nodeBudget rows arity bound ∧ edgeRequests requests ≤ edgeBudget rows arity bound ∧
      after.heap.nodes.next ≤ before.heap.nodes.next + nodeBudget rows arity bound ∧
      after.heap.edges.next ≤ before.heap.edges.next + edgeBudget rows arity bound := by
  obtain ⟨output, after, saved, actual, stable, effects, finalPhysical, finalProfiles, finalAvailable, finalProfile, finalHeight⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.finite clear input before memo ready physical profiles available
      rows arity bound profile heightBound
  have counted := SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer.call_budget actual.graph
    ready.semantic ready.costs physical profiles available
  obtain ⟨requests, trace, nodes, edges⟩ := counted.2.2.2.2 rows arity bound profile heightBound
  have supplies := trace.next_le
  exact ⟨output, after, saved, requests, actual, stable, effects, finalPhysical, finalProfiles,
    finalAvailable, finalProfile, finalHeight, trace, nodes, edges, by omega, by omega⟩

/-- Empty tables derive the initial physical and profile storage obligations. -/
theorem cold (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved requests,
      SourceCurrentAllocatedMergeGraph.Call clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input ∧ Trace before.heap after.heap requests ∧
      nodeRequests requests ≤ nodeBudget rows arity bound ∧ edgeRequests requests ≤ edgeBudget rows arity bound ∧
      after.heap.nodes.next ≤ before.heap.nodes.next + nodeBudget rows arity bound ∧
      after.heap.edges.next ≤ before.heap.edges.next + edgeBudget rows arity bound :=
  finite clear input before SourceCurrentMemoMergeGraph.empty ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap)
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.empty_stored available rows arity bound profile heightBound

/-- Initial headroom bounds both final supplies at the same constructed return. -/
theorem capacity (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (profiles : Profiles memo)
    (available : Available before.heap input) (rows arity bound bits : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound)
    (nodeHeadroom : before.heap.nodes.next + nodeBudget rows arity bound ≤ 2 ^ bits)
    (edgeHeadroom : before.heap.edges.next + edgeBudget rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ output after saved requests,
      StableCall clear input before memo output after saved ∧ Profiles saved ∧ Available after.heap output ∧
      NodeShape (envelope rows bound) arity output ∧ height output ≤ height input ∧
      Trace before.heap after.heap requests ∧ nodeRequests requests ≤ nodeBudget rows arity bound ∧
      edgeRequests requests ≤ edgeBudget rows arity bound ∧
      after.heap.nodes.next ≤ 2 ^ bits ∧ after.heap.edges.next ≤ 2 ^ (bits + 2) := by
  obtain ⟨output, after, saved, requests, _actual, stable, _effects, _physical, finalProfiles,
    finalAvailable, finalProfile, finalHeight, trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    finite clear input before memo ready physical profiles available rows arity bound profile heightBound
  exact ⟨output, after, saved, requests, stable, finalProfiles, finalAvailable, finalProfile, finalHeight,
    trace, nodes, edges, Nat.le_trans nodeSupply nodeHeadroom, Nat.le_trans edgeSupply edgeHeadroom⟩

section CallerScope
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedPartialInvariant (Context Post)
variable {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The same constructed full caller retains its semantic postcondition and actual request budget. -/
theorem caller_finite {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : Caller width} {input : Value Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (profiles : Profiles before.merge)
    (available : Available before.checked.native.machine.heap input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved final requests,
      StableCall literalClear input (physical before.checked) before.merge output after saved ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) before.fourth saved) final ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input ∧ Trace before.checked.native.machine.heap after.heap requests ∧
      nodeRequests requests ≤ nodeBudget rows arity bound ∧ edgeRequests requests ≤ edgeBudget rows arity bound ∧
      after.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget rows arity bound ∧
      after.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget rows arity bound ∧
      ∀ ambient, SourceCurrentMemoMergeLanguage.Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output := by
  obtain ⟨output, after, saved, final, stable, post, finalProfiles, finalAvailable, finalProfile, finalHeight, included⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.caller_finite formulas solver initial profiles available
      rows arity bound profile heightBound
  obtain ⟨workBound, selectionBound, execution⟩ := stable
  have actual := SourceCurrentAllocatedMergeWorkerSound.call_sound
    (execution workBound selectionBound (Nat.le_refl _) (Nat.le_refl _))
  have counted := SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer.call_budget actual.graph
    initial.ready.semantic initial.ready.costs initial.stored profiles available
  obtain ⟨requests, trace, nodes, edges⟩ := counted.2.2.2.2 rows arity bound profile heightBound
  have supplies := trace.next_le
  simp only [SourceCurrentAllocatedNativeEffects.physical] at supplies
  exact ⟨output, after, saved, final, requests, ⟨workBound, selectionBound, execution⟩, post,
    finalProfiles, finalAvailable, finalProfile, finalHeight, trace, nodes, edges, by omega, by omega, included⟩

end CallerScope
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetFinite
