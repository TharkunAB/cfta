import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer

namespace MergeProfileProducerKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open MergedOrdinaryHeight (height)
namespace Producer
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer (cold call_profile)
end Producer
namespace Physical
export SourceCurrentMemoMergeEffects (Stored)
end Physical
namespace Profiles
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache (Stored Certificate)
end Profiles
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A cold actual producer derives output shape and both returned table invariants. -/
theorem cold_output_and_tables {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    Physical.Stored after saved ∧ Profiles.Stored saved ∧ Available after output ∧
      NodeShape (envelope rows bound) arity output ∧ height output ≤ height input := by
  have result := Producer.cold actual semantic costs available
  have outputProfile := result.2.2.2.2 rows arity bound profile bounded
  exact ⟨result.2.1, result.2.2.1, result.2.2.2.1.1, outputProfile⟩

/-- An actual body produces its winner, and a constructed warm call uses the identical state. -/
theorem actual_miss_then_warm {clear : Guard → Bool} {top : Guard}
    {input candidate : Value Symbol Guard} {before after : State Symbol Guard} {current : Memo Symbol Guard}
    (body : Run clear top (SourceCurrentMemoMergeGraph.body top input) before empty candidate after current)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    let saved := remember current input candidate
    let output := (winner current input candidate).result
    Call clear top input before empty output after saved ∧
      Call clear top input after saved output after saved ∧
      Physical.Stored after saved ∧ Profiles.Stored saved ∧
      NodeShape (envelope rows bound) arity output ∧ height output ≤ height input := by
  dsimp only
  have first : Call clear top input before empty (winner current input candidate).result
      after (remember current input candidate) := .miss rfl body
  have result := Producer.cold first semantic costs available
  have warm : Call clear top input after (remember current input candidate)
      (winner current input candidate).result after (remember current input candidate) :=
    .hit (winner_found current input candidate)
  have repeated := Producer.call_profile warm result.1.semantic result.1.costs result.2.1 result.2.2.1
    (result.1.keeps.available input available)
  exact ⟨first, warm, repeated.2.1, repeated.2.2.1,
    repeated.2.2.2.2 rows arity bound profile bounded⟩

/-- Reentrant first-winner readback derives its profile from the actual body, without a candidate law. -/
theorem actual_reentrant_winner {clear : Guard → Bool} {top : Guard}
    {input candidate : Value Symbol Guard} {before after : State Symbol Guard}
    {current : Memo Symbol Guard} {entry : Entry Symbol Guard}
    (body : Run clear top (SourceCurrentMemoMergeGraph.body top input) before empty candidate after current)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (found : current input.referenceOf = some entry) :
    remember current input candidate = current ∧ winner current input candidate = entry ∧
      Physical.Stored after current ∧ Profiles.Stored current ∧ Profiles.Certificate input entry.result := by
  have actual : Call clear top input before empty (winner current input candidate).result
      after (remember current input candidate) := .miss rfl body
  have result := Producer.cold actual semantic costs available
  have retained := winner_existing current input candidate entry found
  refine ⟨retained.1, retained.2, ?_, ?_, ?_⟩
  · simpa only [retained.1] using result.2.1
  · simpa only [retained.1] using result.2.2.1
  · simpa only [retained.2] using result.2.2.2.2

end MergeProfileProducerKernels

#check @MergeProfileProducerKernels.cold_output_and_tables
#print axioms MergeProfileProducerKernels.cold_output_and_tables
#check @MergeProfileProducerKernels.actual_miss_then_warm
#print axioms MergeProfileProducerKernels.actual_miss_then_warm
#check @MergeProfileProducerKernels.actual_reentrant_winner
#print axioms MergeProfileProducerKernels.actual_reentrant_winner
