import MicroCFTA.SourcePruningEnumerationParentProjectionPrimitives
import MicroCFTA.SourceCurrentMemoMergeEffects
import MicroCFTA.SourceCurrentAllocatedMergeGraph
import MicroCFTA.SourceCurrentMergedHeapEffects

/-!
# Projectability through actual memo-aware merge calls

This draft follows the actual recorded worker endpoints.
It does not assert completion of an arbitrary native prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationMemoMergeProjectionHeap
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
namespace Physical
export SourceCurrentMemoMergeEffects (Stored Contract Certified Effect run_effects body_certified)
end Physical
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol : Type}

private theorem top_projectable :
    SourcePruningEnumerationConstraint.project (top : Guard) ≠ none := by
  change (some ([], none) : Option (List EqualityTrie.Trie × Option Guard)) ≠ none
  intro impossible
  cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Checks (clear : Guard → Bool) : Code Symbol Guard Output → Prop
  | .pure _ | .select _ | .request _ => True
  | .work job => SourceEqualityAnnotationHeap.SafeWork (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) job
  | .bind first next => Checks clear first ∧
      ∀ value before middle memo saved,
        Run clear top first before memo value middle saved → Checks clear (next value)

private theorem map_checks (clear : Guard → Bool) (call : Input → Code Symbol Guard Output) (inputs : List Input)
    (checked : ∀ input ∈ inputs, Checks clear (call input)) : Checks clear (map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨checked first List.mem_cons_self, fun _ _ _ _ _ _ =>
        ⟨ih (fun input member => checked input (List.mem_cons_of_mem _ member)), fun _ _ _ _ _ _ => trivial⟩⟩

private theorem retained_checks (clear : Guard → Bool) (values : List (Value Symbol Guard)) :
    Checks clear (retainedColumn values) := by
  have branches (values : List (Value Symbol Guard)) :
      Checks clear (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact SourceEqualityAnnotationHeap.makeUnion (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) values
    · exact ⟨SourceEqualityAnnotationHeap.makeNode (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) _, fun _ _ _ _ _ _ => trivial⟩
  cases values with
  | nil => exact branches []
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact branches (first :: second :: rest)

private theorem small_checks (clear : Guard → Bool) (edge : EdgeValue Symbol Guard)
    (checked : SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) :
    Checks clear (small edge) := by
  refine ⟨map_checks clear Code.request edge.children (fun _ _ => trivial), ?_⟩
  intro children _ _ _ _ _
  exact SourceEqualityAnnotationHeap.makeEdge _ _ _ children checked

private theorem column_checks (clear : Guard → Bool) (values : List (Value Symbol Guard)) :
    Checks clear (column values) :=
  ⟨trivial, fun retained _ _ _ _ _ => retained_checks clear retained⟩

private theorem large_checks (clear : Guard → Bool) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Checks clear (large top first rest) :=
  ⟨map_checks clear column _ (fun values _ => column_checks clear values), fun children _ _ _ _ _ =>
    SourceEqualityAnnotationHeap.makeEdge _ _ _ children top_projectable⟩

private theorem group_checks (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (checked : ∀ edge ∈ edges, SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) : Checks clear (group top edges) := by
  unfold group
  split
  · exact map_checks clear small edges (fun edge member => small_checks clear edge (checked edge member))
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_checks clear first rest, fun _ _ _ _ _ _ => trivial⟩

private theorem root_checks (clear : Guard → Bool) (groups : List (List (EdgeValue Symbol Guard)))
    (checked : ∀ group ∈ groups, ∀ edge ∈ group, SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) :
    Checks clear (root top groups) :=
  ⟨map_checks clear (group top) groups (fun group member => group_checks clear group (checked group member)),
    fun rows _ _ _ _ _ => SourceEqualityAnnotationHeap.makeNode _ rows.flatten⟩

private theorem body_checks (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (heap : Heap before) (available : Available before input) :
    Checks clear (body top input) := by
  cases input with
  | empty | reference | union | mu => trivial
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have resident := InternedEdgeResidency.resident_edges before
          semantic.ready.semantic.1.normal.facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        apply root_checks
        intro chosen member edge included
        have original : edge ∈ edges :=
          grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨chosen, member, included⟩)
        exact heap edge.entry.key edge (resident edge original)
      · simp only [body, closed, ite_false, Checks]

private theorem run_heap
    {clear : Guard → Bool} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Physical.Stored before memo →
      Physical.Certified Physical.Contract clear code before post → Checks clear code → Heap before → Heap after := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Physical.Stored before memo → Available before input → Heap before → Heap after) with
  | pure value state memo =>
      intro post semantic costs stored certified checked heap
      exact heap
  | work job state memo =>
      intro post semantic costs stored certified checked heap
      exact SourceEqualityAnnotationHeap.run _ job checked state heap
  | select fuel done =>
      intro post semantic costs stored certified checked heap
      exact (SourceCurrentMergedHeapEffects.select_effect (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) _ fuel _ _ semantic costs certified.1 _ _ done).annotations heap
  | request actual ih =>
      intro post semantic costs stored certified checked heap
      exact ih semantic costs stored certified.1 heap
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored certified checked heap
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := certified
      have middleHeap := ihFirst intermediate semantic costs stored firstChecked checked.1 heap
      obtain ⟨effect, retained, valid⟩ := Physical.run_effects first intermediate semantic costs stored firstChecked
      exact ihLater post effect.semantic effect.costs retained (nextChecked _ _ effect valid)
        (checked.2 _ _ _ _ _ first) middleHeap
  | hit found =>
      rename_i semantic costs stored available heap
      exact heap
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available heap
      exact ih _ semantic costs stored (Physical.body_certified clear top input before semantic costs available)
        (body_checks clear input before semantic heap available) heap

/-- The actual completed memo call derives projectability of every old and newly stored edge record. -/
theorem call_heap
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Physical.Stored before memo) (available : Available before input)
    (heap : Heap before) : Heap after :=
  run_heap (.request actual) (fun after output => Physical.Contract input before output after)
    semantic costs stored ⟨available, fun _ _ _ returned => returned⟩ trivial heap

end MicroCFTA.SourcePruningEnumerationMemoMergeProjectionHeap

namespace MicroCFTA.SourcePruningEnumerationAllocatedMergeProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Erasure retains the actual constructor heap; separate Top allocation changes only equality state. -/
theorem call_heap
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : SourceCurrentAllocatedMergeGraph.State} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.heap memo) (available : Available before.heap input)
    (heap : Heap before.heap) : Heap after.heap :=
  SourcePruningEnumerationMemoMergeProjectionHeap.call_heap actual.graph ready.semantic ready.costs stored available heap

end MicroCFTA.SourcePruningEnumerationAllocatedMergeProjectionHeap
