import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer
import MicroCFTA.SourceCurrentAllocatedMergeWorkerActual

/-!
# Constructed allocated Merge returns with produced profiles

The actual allocated call retains the heap, output, and completed table.
Finite endpoints construct their own call and stable literal return.
The profile follows the exact winning result at that same returned state.
Constructor reservation bounds remain a separate obligation.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache (Certificate)
open SourceCurrentAllocatedMergeWorkerCompletion (StableCall)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The allocated erasure retains the certificate of its actual winning result. -/
theorem allocated {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : Physical} {memo saved : Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (profiles : Profiles memo)
    (available : Available before.heap input) :
    SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ Certificate input output := by
  have effects := actual.verified ready physical available
  obtain ⟨_effect, finalPhysical, finalProfiles, physicalResult, certificate⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.call_profile actual.graph
      ready.semantic ready.costs physical profiles available
  exact ⟨effects.1, finalPhysical, finalProfiles, physicalResult.1, certificate⟩

/-- Initial profiles construct the allocated call, stable worker return, and returned profile. -/
theorem finite (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (profiles : Profiles memo)
    (available : Available before.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved, SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved ∧
      StableCall clear input before memo output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input := by
  obtain ⟨output, after, saved, actual, _⟩ :=
    SourceCurrentAllocatedMergePhysical.call_complete clear input before memo ready physical available
  obtain ⟨effects, finalPhysical, finalProfiles, finalAvailable, certificate⟩ :=
    allocated actual ready physical profiles available
  have result := certificate rows arity bound profile heightBound
  exact ⟨output, after, saved, actual, SourceCurrentAllocatedMergeWorkerCompletion.call_complete actual,
    effects, finalPhysical, finalProfiles, finalAvailable, result⟩

/-- Empty completed tables derive both initial storage invariants. -/
theorem cold (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved,
      SourceCurrentAllocatedMergeGraph.Call clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input :=
  finite clear input before SourceCurrentMemoMergeGraph.empty ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap)
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.empty_stored available rows arity bound profile heightBound

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

/-- A constructed literal caller retains its full semantic postcondition and produced profile. -/
theorem caller_finite {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : Caller width} {input : Value Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (profiles : Profiles before.merge)
    (available : Available before.checked.native.machine.heap input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved final,
      StableCall literalClear input (physical before.checked) before.merge output after saved ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) before.fourth saved) final ∧
      Profiles saved ∧ Available after.heap output ∧ NodeShape (envelope rows bound) arity output ∧
      height output ≤ height input ∧
      ∀ ambient, SourceCurrentMemoMergeLanguage.Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output := by
  obtain ⟨output, after, saved, final, workBound, selectionBound, stable, post, _resident, _closed, included⟩ :=
    SourceCurrentAllocatedMergeWorkerActual.finite formulas solver initial available
  have actual := SourceCurrentAllocatedMergeWorkerSound.call_sound
    (stable workBound selectionBound (Nat.le_refl _) (Nat.le_refl _))
  obtain ⟨_effects, _finalPhysical, finalProfiles, finalAvailable, certificate⟩ :=
    allocated actual ⟨initial.ready.semantic, initial.ready.costs, initial.ready.good.operations, initial.ready.good.fields⟩
      initial.stored profiles available
  have result := certificate rows arity bound profile heightBound
  exact ⟨output, after, saved, final, ⟨workBound, selectionBound, stable⟩, post,
    finalProfiles, finalAvailable, result.1, result.2, included⟩

end CallerScope
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite
