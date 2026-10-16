import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity

namespace MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceCurrentRequiredQueryMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq (EdgeKey Symbol Guard)]

-- The supplied receipt's same compiled graph derives physical effects and final tables together.
theorem same_required_graph {paths : List (List Int)} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {memos final : Memos}
    (reads : RequireAllReads paths values results before after memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Values after results := by
  have checked := SourceCurrentAllocatedRequiredReadValidity.required reads semantic costs available valid
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [RequireAllReads, compiled] at reads
      obtain ⟨actual, supplied⟩ := reads
      have physical := SourceCurrentRequiredHeapEffects.children (fun _ => True) actual semantic costs
        (by intro _ _ _; trivial) available
      exact ⟨checked.1, checked.2.1, checked.2.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2.2⟩

-- A second supplied required call uses the first call's derived tables and current heap facts.
theorem two_required_calls {firstPaths nextPaths : List (List Int)} {values middleValues results : List (Value Symbol Guard)}
    {before middle after : State Symbol Guard} {memos middleMemo final : Memos}
    (first : RequireAllReads firstPaths values middleValues before middle memos middleMemo)
    (second : RequireAllReads nextPaths middleValues results middle after middleMemo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Keeps before after ∧ Values after results := by
  have initial := same_required_graph first semantic costs available valid
  have later := same_required_graph second initial.2.2.2.2.1 initial.2.2.2.2.2.1 initial.2.2.2.2.2.2 initial.1
  exact ⟨later.1, extends_trans initial.2.1 later.2.1, later.2.2.1.trans initial.2.2.1,
    initial.2.2.2.1.trans later.2.2.2.1, later.2.2.2.2.2.2⟩

-- One selected original position derives its own final tables before the remaining child positions.
theorem selected_position {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard}
    {values results : List (Value Symbol Guard)} {before middle after : State Symbol Guard}
    {found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed}
    {firstTrace : RequireNode needed value before result middle}
    {restTrace : RequireChildren entries (index + 1) values middle results after} {memos middleMemo final : Memos}
    (first : NodeReads firstTrace memos middleMemo) (rest : ChildrenReads restTrace middleMemo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before (value :: values))
    (valid : Valid before memos) :
    ChildrenReads (.selected index found firstTrace restTrace) memos final ∧
      Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have supplied : ChildrenReads (.selected index found firstTrace restTrace) memos final := .selected (found := found) first rest
  exact ⟨supplied, SourceCurrentAllocatedRequiredReadValidity.children supplied semantic costs available valid⟩

end MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes

#print axioms MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.same_required_graph
#print axioms MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.two_required_calls
#print axioms MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.selected_position
#check @MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.same_required_graph
#check @MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.two_required_calls
#check @MicroCFTA.SourceCurrentAllocatedRequiredReadValidityProbes.selected_position
