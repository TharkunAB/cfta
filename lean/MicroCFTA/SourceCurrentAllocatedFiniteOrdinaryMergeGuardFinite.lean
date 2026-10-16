import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer
import MicroCFTA.SourceCurrentAllocatedMergeWorkerActual

/-!
# Constructed Merge returns with hereditary guard bounds

Allocated graph erasure retains each literal heap, result, and memo.
The producer derives the universal law of the exact stored winner.
Finite endpoints construct their own graph and stable literal return.
They need no output bound, future capacity, or recursive callback law.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardFinite
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedMergeWorkerCompletion (StableCall)
open SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache (Certificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Node" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual allocated call derives the universal law of the same winning record. -/
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
    SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.call_guard actual.graph
      ready.semantic ready.costs physical profiles available
  exact ⟨effects.1, finalPhysical, finalProfiles, physicalResult.1, certificate⟩

/-- Initial hereditary input bounds construct the exact allocated graph and literal return. -/
theorem finite (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (profiles : Profiles memo)
    (available : Available before.heap input) (limits : Limits) (profile : Node limits input) :
    ∃ output after saved, SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved ∧
      StableCall clear input before memo output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ Certificate input output ∧ Node limits output := by
  obtain ⟨output, after, saved, actual, _⟩ :=
    SourceCurrentAllocatedMergePhysical.call_complete clear input before memo ready physical available
  obtain ⟨effects, finalPhysical, finalProfiles, finalAvailable, certificate⟩ :=
    allocated actual ready physical profiles available
  exact ⟨output, after, saved, actual, SourceCurrentAllocatedMergeWorkerCompletion.call_complete actual,
    effects, finalPhysical, finalProfiles, finalAvailable, certificate, certificate limits profile⟩

/-- Empty completed tables derive all initial cache certificates. -/
theorem cold (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap input) (limits : Limits) (profile : Node limits input) :
    ∃ output after saved,
      SourceCurrentAllocatedMergeGraph.Call clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      Profiles saved ∧ Available after.heap output ∧ Certificate input output ∧ Node limits output :=
  finite clear input before SourceCurrentMemoMergeGraph.empty ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap)
    SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.empty_stored available limits profile

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardFinite
