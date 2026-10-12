import MicroCFTA.EqualityLeafProjectionEditParent
import MicroCFTA.EqualityLeafProjectionEditSyntax
import MicroCFTA.EqualityLeafProjectionLeafEdit

/-!
# Complete occurrence correspondence for simultaneous leaf edits

Structural recursion composes local leaf intersections with actual ordered
source edits. Selected paths end at leaf domains. The worker runs first;
finite later preparation represents its already returned complete record.
The worker in this module builds finite leaf targets. A source closure that
retains a physical target requires a separate represented-target adapter.
-/
namespace MicroCFTA.EqualityLeafProjectionEditExact
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Edge Path Admissible)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionEditAvailability EqualityLeafProjectionEditTransport

/-- Exact local leaf intersections and actual cache construction derive full
recursive correspondence for every admissible finite occurrence tree. -/
theorem edit_transport [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf)
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (meetAvailable : MeetAvailable meet)
    (join : Leaf → Leaf → Leaf) (leafEdits : ∀ input, Transport leaf meet join (.leaf input))
    (tree : Tree (Tag Symbol Guard) Leaf) : Transport leaf meet join tree := by
  intro edits admissible state facts value represented
  cases edits with
  | nil =>
      refine ⟨state, value, facts, ?_, ?_, ?_⟩
      · simpa only [edit_unselected, run] using grows_refl state
      · simp only [edit_unselected, run]
      simpa only [EqualityLeafProjectionEditSyntax.edit_nil] using represented
  | cons first rest =>
      cases tree with
      | empty =>
          have same : value = .empty := (congrArg (fun result : Value Symbol Guard × State Symbol Guard => result.1) represented).symm
          subst value
          exact ⟨state, .empty, facts, by simpa only [edit_empty, run] using grows_refl state, by simp [edit_empty, run], rfl⟩
      | leaf input => exact leafEdits input (first :: rest) admissible state facts value represented
      | node edges =>
          apply EqualityLeafProjectionEditParent.node leaf leafAvailable leafOrdinary meet meetAvailable join edges ?_
            first rest admissible state facts value represented
          intro edge member child present
          exact edit_transport leaf leafAvailable leafOrdinary meet meetAvailable join leafEdits child
termination_by sizeOf tree
decreasing_by
  have edgeSmall := List.sizeOf_lt_of_mem member
  cases edge with
  | mk tag children =>
      have childSmall := List.sizeOf_lt_of_mem present
      simp only [EqualityLeafProjectionSyntax.Edge.children] at childSmall
      simp_wf
      simp only [EqualityLeafProjectionSyntax.Edge.mk.sizeOf_spec] at edgeSmall
      subst tree
      simp only [EqualityLeafProjectionSyntax.Tree.node.sizeOf_spec]
      omega

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- Actual finite raw leaf construction discharges all local cache and intersection premises. -/
theorem raw_transport
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols)) :
    Transport EqualityRawLeafCompiler.build EqualityRawLeafCompiler.meet EqualityRawLeafInventory.intersect tree :=
  edit_transport EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available
    EqualityRawLeafCompiler.leaves_ordinary EqualityRawLeafCompiler.meet EqualityRawLeafCompiler.meet_available
    EqualityRawLeafInventory.intersect
    (fun input edits _ state facts value represented => by
      have checked := EqualityLeafProjectionLeafEdit.raw_leaf_edit input edits state facts value represented
      cases selected : EqualityLeafProjectionSyntax.atRoot edits <;>
        simpa only [EqualityLeafProjectionSyntax.edit, selected] using checked) tree

/-- Compile original raw occurrences, run simultaneous edits with finite leaf
 targets, and represent the exact returned record in a finite later cache. -/
theorem compiled_raw_edit
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols))
    (edits : List (Path × EqualityRawLeafInventory.Leaf initial symbols)) (admissible : Admissible edits tree)
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state) :
    let compiled := run (EqualityLeafProjectionCompile.compile EqualityRawLeafCompiler.build tree) state
    let actual := run (edit EqualityRawLeafCompiler.meet edits compiled.1) compiled.2
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents EqualityRawLeafCompiler.build (EqualityLeafProjectionSyntax.edit EqualityRawLeafInventory.intersect edits tree) after result := by
  let compiled := run (EqualityLeafProjectionCompile.compile EqualityRawLeafCompiler.build tree) state
  have compiledFacts := compile_available EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available tree state facts
  exact raw_transport tree edits admissible compiled.2 compiledFacts.1 compiled.1
    (completed EqualityRawLeafCompiler.build tree state facts.coherent.valid)

end MicroCFTA.EqualityLeafProjectionEditExact
