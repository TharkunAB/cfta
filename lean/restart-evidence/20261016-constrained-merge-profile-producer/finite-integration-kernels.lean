import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProfileBudget

namespace MergeProfileFiniteIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open SourceCurrentAllocatedMergeWorkerCompletion (StableCall)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "Ready" => SourceCurrentConjunctionRowsAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A generated Merge result gives the next native query budget from original limits. -/
theorem generated_native_budget (clear : Guard → Bool) (input right : Value Symbol Guard)
    (before : Physical) (ready : Ready before) (available : Available before.heap input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input)
    (rightProfile : NodeShape rows arity right) (heightBound : height input ≤ bound)
    (rightHeight : height right ≤ bound) :
    ∃ output after saved,
      SourceCurrentAllocatedMergeGraph.Call clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      Profiles saved ∧ Available after.heap output ∧
      SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget output right ≤
        SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget (envelope rows bound) arity bound := by
  obtain ⟨output, after, saved, actual, stable, _effects, _physical, profiles, resident, outputProfile, outputHeight⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.cold clear input before ready available rows arity bound profile heightBound
  have widened := NodeShape.mono right rightProfile
    (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.rows_le_envelope rows bound) (Nat.le_refl _)
  have budget := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.node_budget_le output right outputProfile widened bound
    (Nat.max_le.mpr ⟨Nat.le_trans outputHeight heightBound, rightHeight⟩)
  exact ⟨output, after, saved, actual, stable, profiles, resident, budget⟩

/-- The first constructed return supplies all storage and profile inputs for a second call. -/
theorem serial_generated_profiles (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : Physical) (ready : Ready before) (available : Available before.heap input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ first middle current output after saved,
      StableCall clear input before SourceCurrentMemoMergeGraph.empty first middle current ∧
      StableCall clear first middle current output after saved ∧ Profiles saved ∧ Available after.heap output ∧
      NodeShape (envelope (envelope rows bound) bound) arity output ∧ height output ≤ height input := by
  obtain ⟨first, middle, current, _firstCall, firstStable, effects, physical, profiles, resident, firstProfile, firstHeight⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.cold clear input before ready available rows arity bound profile heightBound
  obtain ⟨output, after, saved, _lastCall, lastStable, _later, _finalPhysical, finalProfiles, finalAvailable, finalProfile, finalHeight⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.finite clear first middle current effects.ready
      physical profiles resident (envelope rows bound) arity bound firstProfile (Nat.le_trans firstHeight heightBound)
  exact ⟨first, middle, current, output, after, saved, firstStable, lastStable,
    finalProfiles, finalAvailable, finalProfile, Nat.le_trans finalHeight firstHeight⟩

/-- A constructed completed owner replays literally at work fuel one with the whole state unchanged. -/
theorem completed_owner_replay (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : Physical) (ready : Ready before) (available : Available before.heap input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    ∃ output after saved,
      StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧ Profiles saved ∧
      NodeShape (envelope rows bound) arity output ∧
      ∀ selectionFuel, SourceCurrentAllocatedMergeWorker.call clear 1 selectionFuel input after saved = .done output after saved := by
  obtain ⟨output, after, saved, actual, stable, _effects, _physical, profiles, _resident, outputProfile, _height⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileFinite.cold clear input before ready available rows arity bound profile heightBound
  obtain ⟨entry, found, same⟩ := actual.graph.present
  refine ⟨output, after, saved, stable, profiles, outputProfile, ?_⟩
  intro selectionFuel
  simpa only [← same] using SourceCurrentAllocatedMergeWorker.call_hit clear 0 selectionFuel input after saved entry found

end MergeProfileFiniteIntegration

#print axioms MergeProfileFiniteIntegration.generated_native_budget
#check @MergeProfileFiniteIntegration.generated_native_budget
#print axioms MergeProfileFiniteIntegration.serial_generated_profiles
#check @MergeProfileFiniteIntegration.serial_generated_profiles
#print axioms MergeProfileFiniteIntegration.completed_owner_replay
#check @MergeProfileFiniteIntegration.completed_owner_replay
