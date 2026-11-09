import MicroCFTA.SourceCurrentConjunctionRequirementDescriptorsSoundness
import MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
import MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects

/-!
# Original descriptor witnesses from actual tuple preparation

A common accepted raw tuple has live combined equality classes. Current
physical readiness supplies the actual equality fold. Literal preparation
then allocates its descriptors without forcing them. The returned handles,
stored cells, physical state, and smaller witnesses refer to that same
allocation. No completed future requirement is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsWitness
open Language EqualityNormalize EqualityReduction
open InternedConstructorTemplates (Value EdgeValue)
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementCellsSoundness (CommonCell)
open SourceCurrentConjunctionRequirementRows
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Accepted original rows derive live classes and smaller witnesses for every unforced descriptor. -/
theorem accepted_descriptors (tuple : List Row) (nonempty : tuple ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning holds ambient) (SourceCurrentConjunctionEquality.edgeView edge) (.node symbol terms)) :
    ∃ constraints, SourceCurrentConjunctionEmptinessRows.combined
        (tuple.map SourceCurrentConjunctionEquality.edgeView) = some constraints ∧
      ∀ cell ∈ descriptors tuple constraints, ∃ part,
        CommonCell holds ambient symbol terms part cell ∧
          part.height < (Term.node symbol terms).height := by
  have satisfied := (SourceCurrentConjunctionEmptinessRows.combined_sat
    (tuple.map SourceCurrentConjunctionEquality.edgeView) (.node symbol terms)).mpr (by
      intro view member
      obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
      exact (accepted edge edgeIn).choose_spec.2.2)
  cases live : SourceCurrentConjunctionEmptinessRows.combined
      (tuple.map SourceCurrentConjunctionEquality.edgeView) with
  | none =>
      rw [live] at satisfied
      exact False.elim satisfied
  | some constraints =>
      have active := SourceCurrentConjunctionEmptinessRows.combined_active
        (tuple.map SourceCurrentConjunctionEquality.edgeView) constraints live
      have classesSat : Satisfies (.node symbol terms) constraints := by
        simpa only [live, SourceEqualityGuardReadback.Sat] using satisfied
      refine ⟨constraints, rfl, ?_⟩
      apply SourceCurrentConjunctionRequirementDescriptorsSoundness.descriptors_witness
        tuple constraints nonempty holds ambient symbol terms _ active classesSat
      intro edge member
      obtain ⟨other, shape, forest, _⟩ := accepted edge member
      have equal := (Term.node.inj shape).2
      change All₂ (meaning holds ambient) edge.children other at forest
      simpa only [← equal] using forest

/-- Actual preparation returns literal handles and descriptors with closed, smaller accepted witnesses. -/
theorem prepareTuple_witness (tuple : List Row) (before : Storage)
    (ready : Ready before.requirements.physical)
    (resident : Edges before.requirements.physical.heap tuple) (closed : ClosedEdges tuple)
    (nonempty : tuple ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning holds ambient) (SourceCurrentConjunctionEquality.edgeView edge) (.node symbol terms)) :
    ∃ constraints, SourceCurrentConjunctionEmptinessRows.combined
        (tuple.map SourceCurrentConjunctionEquality.edgeView) = some constraints ∧
      let current : Cells := {before.requirements with physical :=
        ⟨before.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}
      let allocated := allocateCells (descriptors tuple constraints) current
      prepareTuple tuple before = .done (some allocated.1) {before with requirements := allocated.2} ∧
        allocated.1 = List.range' before.requirements.cells.length (descriptors tuple constraints).length ∧
        allocated.2.cells = before.requirements.cells ++ descriptors tuple constraints ∧
        Ready allocated.2.physical ∧
        ∀ cell ∈ descriptors tuple constraints,
          SourceCurrentConjunctionRequirementCellsClosed.CellClosed cell ∧
            ∃ part, CommonCell holds ambient symbol terms part cell ∧
              part.height < (Term.node symbol terms).height := by
  obtain ⟨constraints, combined, witnesses⟩ := accepted_descriptors tuple nonempty holds ambient symbol terms accepted
  obtain ⟨result, done, valid, _, classes, _, _, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.requirements.physical.heap
      before.requirements.physical.equality ready.valid ready.fields resident
  have folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
      (.ok (some result), (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2) :=
    Prod.ext done rfl
  have live : SourceEqualityInheritedPayload.classes result.payload = some constraints := classes.trans combined
  refine ⟨constraints, combined, ?_⟩
  dsimp only
  refine ⟨prepareTuple_live tuple before _ result constraints folded live,
    allocateCells_handles _ _, allocateCells_order _ _, ?_, ?_⟩
  · rw [allocateCells_physical]
    exact ⟨ready.semantic, ready.costs, valid, fields⟩
  · intro cell member
    exact ⟨SourceCurrentConjunctionRequirementRowsClosed.descriptors_closed tuple constraints closed cell member,
      witnesses cell member⟩

end MicroCFTA.SourceCurrentConjunctionRequirementRowsWitness
