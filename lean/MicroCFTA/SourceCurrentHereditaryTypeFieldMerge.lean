import MicroCFTA.SourceCurrentHereditaryRequiredMerge

/-!
# A selected Type field through actual Required child mutation

The selected field has a local annotation. Other children need no annotation.
Earlier positions must have no selected requirement. The selected position
uses the initial conditional Mu store. Later calls can change arbitrary
Program children and the heap. The returned field keeps its exact index.

These laws concern completed calls. They do not derive the earlier-position
footprint for every reached caller or a conditional Mu store after the tail.
-/
namespace MicroCFTA.SourceCurrentHereditaryTypeFieldMerge
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- A local field survives at its index when earlier positions have no selected call. -/
theorem children_index [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × Needed)} {offset : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries offset values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (index : Nat) {source : Value Symbol Guard} (input : values[index]? = some source)
    (annotated : Annotated valid source)
    (earlier : ∀ position < index, SourceEqualityNeededMap.lookup ((offset + position : Nat) : Int) entries = none) :
    ∃ result, results[index]? = some result ∧ Annotated valid result := by
  induction index generalizing offset values results before after with
  | zero =>
      cases actual with
      | nil => cases input
      | unselected =>
          cases Option.some.inj input
          exact ⟨_, rfl, annotated⟩
      | selected offset found first rest =>
          cases Option.some.inj input
          have returned := SourceCurrentHereditaryRequiredMerge.node valid first semantic costs
            (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored annotated
          exact ⟨_, rfl, returned.2⟩
  | succ index ih =>
      cases actual with
      | nil => cases input
      | unselected offset absent rest =>
          apply ih rest semantic costs
            (fun value member => available value (List.mem_cons_of_mem _ member))
            (fun value member => closed value (List.mem_cons_of_mem _ member)) stored input
          intro position less
          have selected := earlier (position + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 position] using selected
      | selected offset found first rest =>
          have absent := earlier 0 (by omega)
          simp only [Nat.add_zero] at absent
          rw [absent] at found
          cases found

/-- The first Type field survives an actual bounded call with arbitrary later Program work. -/
theorem requireAll_done_head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {fuel readFuel : Nat} {paths : List (List Int)}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    {source : Value Symbol Guard} (input : values[0]? = some source) (annotated : Annotated valid source) :
    ∃ result, results[0]? = some result ∧ Annotated valid result := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, actual⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at graph
      exact children_index valid graph semantic costs available closed stored 0 input annotated
        (by intro position less; omega)

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The actual memo receipt supplies the ordered graph for the same retained field. -/
theorem requireAll_index [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop)
    {paths : List (List Int)} {values results : List (Value CurrentSymbol CurrentGuard)}
    {before after : State CurrentSymbol CurrentGuard} {memos saved : EndpointMemoGateTrace.Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (index : Nat) {source : Value CurrentSymbol CurrentGuard} (input : values[index]? = some source)
    (annotated : Annotated valid source)
    (earlier : ∀ entries, SourceEqualityNeeded.build paths = .node entries →
      ∀ position < index, SourceEqualityNeededMap.lookup (position : Int) entries = none) :
    ∃ result, results[index]? = some result ∧ Annotated valid result := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [SourceCurrentRequiredQueryMemos.RequireAllReads, compiled] at reads
      obtain ⟨actual, _calls⟩ := reads
      exact children_index valid actual semantic costs available closed stored index input annotated
        (by simpa only [Nat.zero_add] using earlier entries compiled)

end MicroCFTA.SourceCurrentHereditaryTypeFieldMerge
