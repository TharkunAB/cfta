import MicroCFTA.SourcePruningEnumerationSelectionArity
import MicroCFTA.SourcePruningEnumerationNativeArityPrimitives

/-!
# Edge-record arity through actual completed merge calls

Small rows retain the guard of their actual original edge.
Their actual ordered map returns the same number of children.
Large rows use the source Top guard.
The proof follows the real intermediate heaps and memo tables.
-/
namespace MicroCFTA.SourcePruningEnumerationMergeArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourcePruningEnumerationArityOrigins (Fits Heap)
open SourceCurrentMemoMergeGraph
namespace Physical
export SourceCurrentMemoMergeEffects (Stored Contract Certified Effect run_effects body_certified)
end Physical
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol : Type}

private theorem top_fits (arity : Nat) : Fits (top : Guard) arity := by
  intro tries residual projected start
  have topProjection : SourcePruningEnumerationConstraint.project (top : Guard) = some ([], none) := rfl
  rw [topProjection] at projected
  have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
  subst tries
  rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem map_length (clear : Guard → Bool) (call : Input → Code Symbol Guard Output)
    (inputs : List Input) {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {outputs : List Output}
    (actual : Run clear top (map call inputs) before memo outputs after saved) : outputs.length = inputs.length := by
  induction inputs generalizing before after memo saved outputs with
  | nil => cases actual; rfl
  | cons first rest ih =>
      cases actual with
      | bind called later =>
          cases later with
          | bind walked returned =>
              cases returned
              exact congrArg Nat.succ (ih walked)

private def Checks (clear : Guard → Bool) : Code Symbol Guard Output → Prop
  | .pure _ | .select _ | .request _ => True
  | .work job => ∀ state, SourcePruningEnumerationNativeArityPrimitives.WorkFits job state
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
    · exact SourcePruningEnumerationNativeArityPrimitives.makeUnion_fits values
    · exact ⟨SourcePruningEnumerationNativeArityPrimitives.makeNode_fits _, fun _ _ _ _ _ _ => trivial⟩
  cases values with
  | nil => exact branches []
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact branches (first :: second :: rest)

private theorem small_checks (clear : Guard → Bool) (edge : EdgeValue Symbol Guard)
    (checked : Fits edge.entry.key.constraint edge.children.length) : Checks clear (small edge) := by
  refine ⟨map_checks clear Code.request edge.children (fun _ _ => trivial), ?_⟩
  intro children before middle memo saved actual state
  apply SourcePruningEnumerationNativeArityPrimitives.makeEdge_fits _ _ children state
  rw [map_length clear Code.request edge.children actual]
  exact checked

private theorem column_checks (clear : Guard → Bool) (values : List (Value Symbol Guard)) :
    Checks clear (column values) :=
  ⟨trivial, fun retained _ _ _ _ _ => retained_checks clear retained⟩

private theorem large_checks (clear : Guard → Bool) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Checks clear (large top first rest) :=
  ⟨map_checks clear column _ (fun values _ => column_checks clear values), fun children _ _ _ _ _ state =>
    SourcePruningEnumerationNativeArityPrimitives.makeEdge_fits _ _ children state (top_fits _)⟩

private theorem group_checks (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (checked : ∀ edge ∈ edges, Fits edge.entry.key.constraint edge.children.length) : Checks clear (group top edges) := by
  unfold group
  split
  · exact map_checks clear small edges (fun edge member => small_checks clear edge (checked edge member))
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_checks clear first rest, fun _ _ _ _ _ _ => trivial⟩

private theorem root_checks (clear : Guard → Bool) (groups : List (List (EdgeValue Symbol Guard)))
    (checked : ∀ group ∈ groups, ∀ edge ∈ group, Fits edge.entry.key.constraint edge.children.length) :
    Checks clear (root top groups) :=
  ⟨map_checks clear (group top) groups (fun group member => group_checks clear group (checked group member)),
    fun rows _ _ _ _ _ => SourcePruningEnumerationNativeArityPrimitives.makeNode_fits rows.flatten⟩

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
        exact heap.edge before semantic.ready.semantic.1.normal.facts.coherent edge (resident edge original)
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
      exact SourcePruningEnumerationNativeArityPrimitives.work_heap job state heap (checked state)
  | select fuel done =>
      intro post semantic costs stored certified checked heap
      exact (SourcePruningEnumerationSelectionArity.select_effect _ fuel _ _ semantic costs certified.1 _ _ done).arity heap
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

/-- The actual completed memo call derives arity of every old and newly stored edge record. -/
theorem call_heap
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Physical.Stored before memo) (available : Available before input)
    (heap : Heap before) : Heap after :=
  run_heap (.request actual) (fun after output => Physical.Contract input before output after)
    semantic costs stored ⟨available, fun _ _ _ returned => returned⟩ trivial heap

end MicroCFTA.SourcePruningEnumerationMergeArity

namespace MicroCFTA.SourcePruningEnumerationAllocatedMergeArity
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
open SourcePruningEnumerationArityOrigins (Heap)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Erasure retains the actual constructor heap; separate Top allocation changes only equality state. -/
theorem call_heap
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : SourceCurrentAllocatedMergeGraph.State} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.heap memo) (available : Available before.heap input)
    (heap : Heap before.heap) : Heap after.heap :=
  SourcePruningEnumerationMergeArity.call_heap actual.graph ready.semantic ready.costs stored available heap

end MicroCFTA.SourcePruningEnumerationAllocatedMergeArity
