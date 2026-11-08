import MicroCFTA.SourceSynthesisProgramHeight
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentHereditaryProgramRequired

/-!
# Program height through actual annotation-only Required work

Only child zero can change. Every later child follows the actual
unselected branch. Row rejection and node normalization can remove rows.
The returned ordinary Program height therefore cannot increase.

These are successful local graph laws. The ordinary input premise excludes
recursive head exposure. No global completion or Type progress follows.
-/
namespace MicroCFTA.SourceSynthesisProgramHeightRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityNeeded (Needed)
open SourceCurrentHereditaryProgramRequired (AnnotationOnly)
local notation "Height" => SourceSynthesisProgramHeight.value
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem tail_identity
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after)
    (only : AnnotationOnly entries) (positive : 0 < index) :
    results = values ∧ after = before := by
  cases actual with
  | nil => exact ⟨rfl, rfl⟩
  | unselected index absent rest =>
      obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
      exact ⟨rfl, rfl⟩
  | selected index found first rest =>
      rw [only index (by omega)] at found
      cases found
termination_by values.length

private theorem children_tail
    {entries : List (Int × Needed)} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard}
    (actual : RequireChildren entries 0 values before results after)
    (only : AnnotationOnly entries) : results.tail = values.tail := by
  cases values with
  | nil => cases actual; rfl
  | cons value values =>
      cases actual with
      | unselected index absent rest =>
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          rfl
      | selected index found first rest =>
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          rfl

private theorem rows_height
    {entries : List (Int × Needed)} {inputs outputs : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard}
    (actual : RequireRows entries inputs before outputs after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before inputs) (only : AnnotationOnly entries) :
    SourceSynthesisProgramHeight.edges outputs ≤ SourceSynthesisProgramHeight.edges inputs := by
  cases inputs with
  | nil => cases actual; exact Nat.le_refl _
  | cons edge inputs =>
      cases actual with
      | rejected doesNotFit rest =>
          have later := rows_height rest semantic costs
            (fun row member => resident row (List.mem_cons_of_mem _ member)) only
          simpa only [SourceSynthesisProgramHeight.edges] using
            Nat.le_trans later (Nat.le_max_right (SourceSynthesisProgramHeight.edge edge)
              (SourceSynthesisProgramHeight.edges inputs))
      | @kept _ _ values middle result afterEdge _ _ _ _ doesFit adjusted built rest =>
          have facts := semantic.ready.semantic.1.normal.facts
          have available : Values before edge.children :=
            facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
          have physical := SourceCurrentRequiredHeapEffects.children (fun _ => True) adjusted semantic costs
            (by intro _ _ _; trivial) available
          have constructed := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint
            values middle physical.2.1.ready physical.2.2.2.2
          have afterSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
            values middle physical.2.1 physical.2.2.2.2
          rw [built] at afterSemantic
          have edgeKept := constructed.1
          rw [built] at edgeKept
          have readback := MergedPhysicalGroupEdges.makeEdge_fields middle
            physical.2.1.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint
            values physical.2.2.2.2
          rw [built] at readback
          have own := SourceSynthesisProgramHeight.edge_same_tail edge result
            ((congrArg List.tail readback.2.2).trans (children_tail adjusted only))
          have afterCosts : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 :=
            physical.2.2.1
          rw [built] at afterCosts
          have growth := physical.1.trans edgeKept
          have later := rows_height rest afterSemantic afterCosts
            (fun row member => InternedEdgeResidency.edge_grows _ _ growth.growth row
              (resident row (List.mem_cons_of_mem _ member))) only
          simp only [SourceSynthesisProgramHeight.edges]
          rw [own]
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans later (Nat.le_max_right _ _)⟩
termination_by inputs.length

/-- Actual annotation-only Required work cannot increase an ordinary Program height. -/
theorem node
    {entries : List (Int × Needed)} {input output : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) input before output after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (ordinary : SourceEqualityRequiredCache.Ordinary input) (only : AnnotationOnly entries) :
    Height output ≤ Height input := by
  cases input with
  | empty =>
      cases actual with
      | identity | empty => exact Nat.le_refl _
      | recursive nonempty recursive head body => cases recursive
  | reference name => cases ordinary
  | union entry members depth free => cases ordinary
  | mu entry body depth ordinaryShape => cases ordinary
  | node entry inputs depth free =>
      cases actual with
      | identity => exact Nat.le_refl _
      | ordinary nonempty adjusted built =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have bounded := rows_height adjusted semantic costs resident only
          have physical := SourceCurrentRequiredHeapEffects.rows (fun _ => True) adjusted semantic costs
            (by intro _ _ _; trivial) resident
          have returned := SourceSynthesisProgramHeight.makeNode_le _ _
            physical.2.1.ready.semantic.1.normal.facts physical.2.2.2.2
          rw [built] at returned
          simpa only [SourceSynthesisProgramHeight.value] using
            Nat.le_trans returned (Nat.add_le_add_left bounded 1)
      | recursive nonempty recursive head body => cases recursive

end MicroCFTA.SourceSynthesisProgramHeightRequired
