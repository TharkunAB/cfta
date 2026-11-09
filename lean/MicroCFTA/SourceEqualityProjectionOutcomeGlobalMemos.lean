import MicroCFTA.SourceEqualityProjectionOutcomeMemos
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Global memo bundles at every actual projection outcome

The receipt retains every ordered unfolding call, including calls before
failure. Both query tables stay exact and remain valid at the same actual
returned heap. Current readiness, costs and residency derive this bundle.
No completed projection graph or future memo bundle is supplied.
-/
namespace MicroCFTA.SourceEqualityProjectionOutcomeGlobalMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionOutcomePrimitives (reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The same bounded forest call retains ordered unfoldings and both query tables. -/
def ForestReads (p h : Nat) (path : List Int) (values : List Node)
    (before : State Symbol Guard) (memos saved : Memos) : Prop :=
  SourceEqualityProjectionOutcomeMemos.ForestReads p h path values before memos.unfolding saved.unfolding ∧
    saved.query = memos.query

/-- Every actual forest outcome derives a valid final bundle and retains completed entries. -/
theorem forest_memos (p h : Nat) (path : List Int) (values : List Node) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ForestReads p h path values before memos saved ∧
      Valid (reached (SourceEqualityProjectionWorker.forest p h path values before)) saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨saved, calls, coherent, retained⟩ := SourceEqualityProjectionOutcomeMemos.forest_memos
    p h path values before semantic costs available memos.unfolding valid.unfolding
  have effects := SourceEqualityProjectionOutcomeMemos.forest_effects p h path values before semantic costs available
  exact ⟨{memos with unfolding := saved}, ⟨calls, rfl⟩,
    ⟨coherent, SourceEndpointMemo.grows before _ effects.1.growth effects.1.history memos.query valid.query⟩,
    retained, rfl⟩

end MicroCFTA.SourceEqualityProjectionOutcomeGlobalMemos
