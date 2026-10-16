import MicroCFTA.SourceCurrentAllocatedProjectionReadValidity
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity

namespace MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityProjectionMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

-- One supplied forest receipt derives physical availability and its own final global tables.
theorem same_forest_graph {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} {trace : Forest path values before result after} {memos final : Memos}
    (reads : SourceEqualityQueryGlobalMemos.ProjectionReads trace memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result := by
  have checked := SourceCurrentAllocatedProjectionReadValidity.forest reads semantic costs available valid
  have physical := SourceEqualityProjectionCosts.forest_effects trace semantic costs available
  exact ⟨checked.1, checked.2.1, checked.2.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

-- A reached required call consumes the projection's actual returned heap and memo bundle.
theorem projection_then_required {path : List Int} {requiredPaths : List (List Int)}
    {values results : List (Value Symbol Guard)} {projected : Value Symbol Guard}
    {before middle after : State Symbol Guard} {trace : Forest path values before projected middle}
    {memos middleMemo final : Memos}
    (first : SourceEqualityQueryGlobalMemos.ProjectionReads trace memos middleMemo)
    (next : SourceCurrentRequiredQueryMemos.RequireAllReads requiredPaths [projected] results middle after middleMemo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have initial := same_forest_graph first semantic costs available valid
  have projectedAvailable : Values middle [projected] := by
    intro value member
    have same : value = projected := List.mem_singleton.mp member
    subst value
    exact initial.2.2.2.2.2.2
  have later := SourceCurrentAllocatedRequiredReadValidity.required next initial.2.2.2.2.1
    initial.2.2.2.2.2.1 projectedAvailable initial.1
  exact ⟨later.1, extends_trans initial.2.1 later.2.1, later.2.2.trans initial.2.2.1⟩

-- A root union uses the first row read's returned table for the second and then only constructs a node.
theorem root_two_ordered_reads {first second result : Value Symbol Guard}
    {before middle afterReads after : State Symbol Guard} {left right : List (EdgeValue Symbol Guard)}
    {firstTrace : Read first before left middle} {secondTrace : Read second middle right afterReads}
    {memos : Memos} {middleMemo finalMemo : UMemo}
    (firstCalls : ReadReads firstTrace memos.unfolding middleMemo)
    (secondCalls : ReadReads secondTrace middleMemo finalMemo)
    (built : run (makeNode (left ++ (right ++ []))) afterReads = (result, after))
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before [first, second])
    (valid : Valid before memos) :
    ∃ actual : Forest [] [first, second] before result after,
      SourceEqualityQueryGlobalMemos.ProjectionReads actual memos { memos with unfolding := finalMemo } ∧
        Valid after { memos with unfolding := finalMemo } ∧ Extends memos.unfolding finalMemo := by
  have calls : ReadAllReads (.cons firstTrace (.cons secondTrace .nil)) memos.unfolding finalMemo :=
    .cons firstCalls (.cons secondCalls .nil)
  have actual : Forest [] [first, second] before result after := .root (.node (.cons firstTrace (.cons secondTrace .nil)) built)
  have supplied : SourceEqualityQueryGlobalMemos.ProjectionReads actual memos { memos with unfolding := finalMemo } :=
    ⟨.root (.node (built := built) calls), rfl⟩
  have checked := SourceCurrentAllocatedProjectionReadValidity.forest supplied semantic costs available valid
  exact ⟨actual, supplied, checked.1, checked.2.1⟩

end MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes

#print axioms MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.same_forest_graph
#print axioms MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.projection_then_required
#print axioms MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.root_two_ordered_reads
#check @MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.same_forest_graph
#check @MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.projection_then_required
#check @MicroCFTA.SourceCurrentAllocatedProjectionReadValidityProbes.root_two_ordered_reads
