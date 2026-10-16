import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer

namespace MergeBudgetProducerKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests nodeReservations edgeReservations)
open MergedOrdinaryHeight (height)
namespace Producer
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer (cold call_budget)
end Producer
namespace Physical
export SourceCurrentMemoMergeEffects (Stored)
end Physical
namespace Profiles
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache (Stored)
end Profiles
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A cold actual call derives its request trace and input-only bounds for both final supplies. -/
theorem cold_requests_and_supplies {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    Physical.Stored after saved ∧ Profiles.Stored saved ∧ ∃ requests,
      Trace before after requests ∧ nodeRequests requests ≤ nodeBudget rows arity bound ∧
      edgeRequests requests ≤ edgeBudget rows arity bound ∧
      after.nodes.next ≤ before.nodes.next + nodeBudget rows arity bound ∧
      after.edges.next ≤ before.edges.next + edgeBudget rows arity bound := by
  have result := Producer.cold actual semantic costs available
  obtain ⟨requests, trace, nodes, edges⟩ := result.2.2.2.2 rows arity bound profile bounded
  have supplies := trace.next_le
  exact ⟨result.2.1, result.2.2.1, requests, trace, nodes, edges, by omega, by omega⟩

/-- A constructed warm hit has an empty Work trace and consumes no identity. -/
theorem warm_hit_zero {clear : Guard → Bool} {top : Guard}
    {input : Value Symbol Guard} {before : State Symbol Guard} {memo : Memo Symbol Guard}
    {entry : Entry Symbol Guard}
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (physical : Physical.Stored before memo) (profiles : Profiles.Stored memo)
    (available : Available before input) (found : memo input.referenceOf = some entry) :
    Call clear top input before memo entry.result before memo ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode.Contract input before entry.result before ∧
      Trace before before [] ∧ nodeReservations ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 ∧
      edgeReservations ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 := by
  have actual : Call clear top input before memo entry.result before memo := .hit found
  have result := Producer.call_budget actual semantic costs physical profiles available
  exact ⟨actual, result.2.2.2, .refl _, rfl, rfl⟩

/-- Keeping an earlier winner does not remove constructor requests from its actual losing body. -/
theorem losing_body_counted {clear : Guard → Bool} {top : Guard}
    {input candidate : Value Symbol Guard} {before after : State Symbol Guard}
    {current : Memo Symbol Guard} {entry : Entry Symbol Guard}
    (body : Run clear top (SourceCurrentMemoMergeGraph.body top input) before empty candidate after current)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (found : current input.referenceOf = some entry)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    remember current input candidate = current ∧ winner current input candidate = entry ∧
      ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ nodeBudget rows arity bound ∧
        edgeRequests requests ≤ edgeBudget rows arity bound ∧
        after.nodes.next = before.nodes.next + nodeReservations requests ∧
        after.edges.next = before.edges.next + edgeReservations requests := by
  have actual : Call clear top input before empty (winner current input candidate).result
      after (remember current input candidate) := .miss rfl body
  have result := Producer.cold actual semantic costs available
  obtain ⟨requests, trace, nodes, edges⟩ := result.2.2.2.2 rows arity bound profile bounded
  have retained := winner_existing current input candidate entry found
  exact ⟨retained.1, retained.2, requests, trace, nodes, edges, trace.next_exact⟩

end MergeBudgetProducerKernels

#check @MergeBudgetProducerKernels.cold_requests_and_supplies
#print axioms MergeBudgetProducerKernels.cold_requests_and_supplies
#check @MergeBudgetProducerKernels.warm_hit_zero
#print axioms MergeBudgetProducerKernels.warm_hit_zero
#check @MergeBudgetProducerKernels.losing_body_counted
#print axioms MergeBudgetProducerKernels.losing_body_counted
