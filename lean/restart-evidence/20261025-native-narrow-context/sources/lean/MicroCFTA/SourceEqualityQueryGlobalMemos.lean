import MicroCFTA.SourceEqualityProjectionMemos
import MicroCFTA.SourceEmptinessProjection

/-!
# Three coherent global tables through actual projection operands

Exposure and path projection perform the recorded global unfolding calls.
They retain both query tables while deriving their coherence in each final
constructor heap. Earlier completed unfolding entries remain unchanged.
The scoped native state advances to that same heap without resetting its
own tables. Native calls, whole-query composition, and GHC publication
remain separate from these projection receipts.
-/
namespace MicroCFTA.SourceEqualityQueryGlobalMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEmptinessProjection
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Exposure retains its actual unfolding calls and leaves both query tables unchanged. -/
def ExposureReads [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (memos saved : Memos) : Prop :=
  SourceEqualityExposureMemos.NodeEdgesReads fuel value state memos.unfolding saved.unfolding ∧ saved.query = memos.query

/-- Forest projection retains each actual unfolding call and both original query tables. -/
def ProjectionReads [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (memos saved : Memos) : Prop :=
  SourceEqualityProjectionMemos.ForestReads trace memos.unfolding saved.unfolding ∧ saved.query = memos.query

/-- A scoped operand retains the projection calls in its exact advanced native state. -/
inductive OperandReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : List Int} → {values : List (Value Symbol Guard)} → {result : Value Symbol Guard} →
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard} →
    Operand path values before result after → Memos → Memos → Prop where
  | force (read : ProjectionReads projection memos saved) : OperandReads (.force projection) memos saved

/-- Every bounded actual exposure derives all three coherent tables without a future-validity premise. -/
theorem exposure_memos [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (costs : CostHeap state) (available : Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, ExposureReads fuel value state memos saved ∧
      Valid (MergedFreshOrdinaryExposure.nodeEdges fuel value state).state saved ∧
      Extends memos.unfolding saved.unfolding := by
  obtain ⟨saved, read, coherent, retained⟩ := SourceEqualityExposureMemos.nodeEdges_reads
    fuel value state semantic costs available memos.unfolding valid.unfolding
  have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value state semantic costs available
  exact ⟨{memos with unfolding := saved}, ⟨read, rfl⟩,
    ⟨coherent, SourceEndpointMemo.grows state _ checked.keeps.growth checked.keeps.history memos.query valid.query⟩,
    retained⟩

/-- An actual forest projection derives all three coherent final tables and retains earlier unfoldings. -/
theorem forest_memos [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ProjectionReads trace memos saved ∧ Valid after saved ∧ Extends memos.unfolding saved.unfolding := by
  obtain ⟨saved, read, coherent, retained⟩ := SourceEqualityProjectionMemos.forest_reads
    trace semantic costs available memos.unfolding valid.unfolding
  have checked := SourceEqualityProjectionCosts.forest_effects trace semantic costs available
  exact ⟨{memos with unfolding := saved}, ⟨read, rfl⟩,
    ⟨coherent, SourceEndpointMemo.grows before after checked.1.growth checked.1.history memos.query valid.query⟩,
    retained⟩

/-- Plain scoped operands derive actual projection calls and coherent global tables without closing the forest. -/
theorem operand_memos [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (semantic : SemanticReady before.machine.heap)
    (costs : CostHeap before.machine.heap) (available : Values before.machine.heap values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, OperandReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding := by
  cases trace with
  | force projection =>
      obtain ⟨saved, read, coherent, retained⟩ := forest_memos projection semantic costs available memos valid
      exact ⟨saved, .force read, coherent, retained⟩

end MicroCFTA.SourceEqualityQueryGlobalMemos
