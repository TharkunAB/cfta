import MicroCFTA.MergedColdMergeCompletion
import MicroCFTA.MergedPrefixHeight
import MicroCFTA.MergedPrefixAtoms
import MicroCFTA.MergedNoNewMu

/-!
# Complete merging with ordinary and union prefix bounds

The source executor derives a stable comparison bound from the input heap.
Its output adds at most one prefix layer and retains the input atoms.
The comparison bound does not bound the work of the enumeration driver.
-/
namespace MicroCFTA.MergedPrefixCompletion
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open MergedPhysicalWarmup MergedColdMerge InternedBoundaryAtoms InternedShallowHeap

variable {Symbol Guard : Type}

/-- Complete source merging derives its comparison bound and its output bounds. -/
theorem source_execute_prefix_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before input) :
    Complete (fun comparison => execute MergedSourceGrouping.groups clear top comparison input)
      before (fun after result => Available after result ∧ NoNewMu before after ∧
        SourceSynthesisUniversePrefixHeight.height result ≤ SourceSynthesisUniversePrefixHeight.height input + 1 ∧
        ∀ atom ∈ atoms result, atom ∈ atoms input) := by
  obtain ⟨bound, result, after, complete, extension, resident⟩ :=
    MergedColdMerge.source_execute_complete clear top input before facts prepared available
  have done := complete bound (Nat.le_refl _)
  have unchanged := MergedNoNewMu.source_execute_noNewMu clear top bound input before facts prepared available
  have origin : NoNewMu before after := by
    simpa only [done, MergedSourceComparison.Result.state] using unchanged
  refine ⟨bound, result, after, complete, extension, resident, origin, ?_, ?_⟩
  · exact MergedPrefixHeight.worker_height MergedSourceGrouping.groups
      MergedSourceGrouping.groups_correct clear top (MergedOrdinaryHeight.height input) bound
      input before result after facts prepared available done
  · exact MergedPrefixAtoms.execute_atoms MergedSourceGrouping.groups
      MergedSourceGrouping.groups_correct clear top bound input before result after facts prepared available done

end MicroCFTA.MergedPrefixCompletion
