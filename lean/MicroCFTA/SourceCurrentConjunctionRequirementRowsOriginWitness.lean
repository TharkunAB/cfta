import MicroCFTA.SourceCurrentConjunctionRequirementRowsWitness
import MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement

/-!
# Accepted witnesses at actual allocated origin handles

Live tuple preparation registers the identical original descriptors at its
returned handles. Each handle retains its smaller common-term claim in the
current refinement invariant. A terminal done lookup then supplies that
same accepted term. Registration needs no future origin or force result.
The terminal lookup and current refinement remain explicit local premises.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsOriginWitness
open Language EqualityNormalize
open InternedConstructorTemplates (Value EdgeValue)
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementCellsSoundness (CommonCell)
open SourceCurrentConjunctionRequirementCellsRefinement (Invariant)
open SourceCurrentConjunctionRequirementRows
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Actual accepted preparation registers each literal descriptor and its smaller witness at the same handle. -/
theorem prepareTuple_origins (tuple : List Row) (before : Storage) (origins : List Cell)
    (refined : Invariant origins before.requirements) (ready : Ready before.requirements.physical)
    (resident : Edges before.requirements.physical.heap tuple) (closed : ClosedEdges tuple)
    (nonempty : tuple ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning holds ambient) (SourceCurrentConjunctionEquality.edgeView edge) (.node symbol terms)) :
    ∃ constraints,
      let current : Cells := {before.requirements with physical :=
        ⟨before.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}
      let added := descriptors tuple constraints
      let allocated := allocateCells added current
      SourceCurrentConjunctionEmptinessRows.combined
          (tuple.map SourceCurrentConjunctionEquality.edgeView) = some constraints ∧
        prepareTuple tuple before = .done (some allocated.1) {before with requirements := allocated.2} ∧
        Invariant (origins ++ added) allocated.2 ∧
        allocated.1 = List.range' before.requirements.cells.length added.length ∧
        allocated.2.cells = before.requirements.cells ++ added ∧
        Ready allocated.2.physical ∧
        ∀ handle ∈ allocated.1, ∃ index cell,
          added[index]? = some cell ∧ handle = before.requirements.cells.length + index ∧
            (origins ++ added)[handle]? = some cell ∧
            SourceCurrentConjunctionRequirementCellsClosed.CellClosed cell ∧
              ∃ part, CommonCell holds ambient symbol terms part cell ∧
                part.height < (Term.node symbol terms).height := by
  obtain ⟨constraints, combined, prepared, handles, cells, postReady, witnesses⟩ :=
    SourceCurrentConjunctionRequirementRowsWitness.prepareTuple_witness tuple before ready resident closed nonempty
      holds ambient symbol terms accepted
  let current : Cells := {before.requirements with physical :=
    ⟨before.requirements.physical.heap,
      (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}
  let added := descriptors tuple constraints
  let allocated := allocateCells added current
  have currentRefined : Invariant origins current := by
    refine ⟨refined.length, ?_⟩
    intro handle original present originFound currentFound
    exact refined.cells handle original present originFound currentFound
  have registered := SourceCurrentConjunctionRequirementRowsRefinement.allocateCells_refinement
    added current origins currentRefined
  refine ⟨constraints, combined, prepared, registered, handles, cells, postReady, ?_⟩
  intro handle member
  rw [handles] at member
  obtain ⟨index, inside, same⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at same
  have exactHandle : handle = before.requirements.cells.length + index := by omega
  have found : added[index]? = some added[index] := List.getElem?_eq_getElem inside
  have identified := SourceCurrentConjunctionRequirementRowsRefinement.allocateCells_origin
    added current origins currentRefined index added[index] found
  have originFound : (origins ++ added)[handle]? = some added[index] := by
    rw [exactHandle]
    exact identified.2
  have common := witnesses added[index] (List.mem_of_getElem? found)
  exact ⟨index, added[index], found, exactHandle, originFound, common⟩

/-- A current done cell accepts every common term retained from its exact registered origin. -/
theorem stored_done_witness (origins : List Cell) (before : Cells) (handle : Nat)
    (original : Cell) (nodes : List Node) (refined : Invariant origins before)
    (originFound : origins[handle]? = some original)
    (currentDone : SourceCurrentConjunctionRequirementCells.lookup handle before = some (.done nodes))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (common : CommonCell holds ambient symbol terms part original) :
    SourceCurrentConjunctionEmptinessRows.Accepts (meaning holds ambient) nodes part :=
  refined.cells handle original (.done nodes) originFound currentDone holds ambient symbol terms part common

end MicroCFTA.SourceCurrentConjunctionRequirementRowsOriginWitness
