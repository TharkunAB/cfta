import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed
import MicroCFTA.SourceCurrentConjunctionRequirementPullSoundness

/-!
# Accepted witnesses through actual requirement-cell forcing

A current column or cached result accepts its common term. A pending cursor
retains the common-term assertion of its actual collected and pending jobs.
The execution bridge transfers that assertion through literal cell forcing.
An original satisfied active class also supplies a strictly smaller witness.
These are local successful-force laws. They do not supply future completion,
adequate native bounds, or semantic origins for a whole stored table.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsSoundness
open Language EqualityNormalize
open InternedConstructorTemplates (Value EdgeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedColdReaderClosedInputs (ClosedValues)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionEmptinessRows (Accepts)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- A current cell retains the accepted common term of its actual descriptor. -/
def CommonCell (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) : Cell → Prop
  | .column nodes | .done nodes => Accepts (meaning holds ambient) nodes part
  | .pending cursor => SourceCurrentConjunctionRequirementPullSoundness.Common
      holds ambient symbol terms part cursor

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Actual successful forcing preserves the common accepted term of the present cell. -/
theorem force_common (annotation : Guard → Prop) {p h handle : Nat} {before after : Cells}
    {cell : Cell} {nodes : List Node}
    (found : SourceCurrentConjunctionRequirementCells.lookup handle before = some cell)
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before = .done nodes after)
    (semantic : SemanticReady before.physical.heap) (costs : CostHeap before.physical.heap)
    (fields : AnnotationHeap annotation before.physical.heap)
    (values : SourceCurrentConjunctionRequirementCellsValues.CellValues before.physical.heap cell)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.CellClosed cell)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (common : CommonCell holds ambient symbol terms part cell) :
    Accepts (meaning holds ambient) nodes part := by
  cases cell with
  | done cached =>
      rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle cached before found] at actual
      cases actual
      exact common
  | column original =>
      have forced : SourceCurrentConjunctionRequirementCells.force p h handle before =
          .done (SourceCurrentConjunctionRequirements.canonical original)
            (SourceCurrentConjunctionRequirementCells.update handle
              (.done (SourceCurrentConjunctionRequirements.canonical original)) before) := by
        rw [SourceCurrentConjunctionRequirementCells.force_step]
        simp only [SourceCurrentConjunctionRequirementCells.forceStep, found]
      rw [forced] at actual
      cases actual
      exact (SourceCurrentConjunctionRequirements.canonical_accepts original before.physical.heap
        semantic values closed holds ambient part).mpr common
  | pending cursor =>
      have ran := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
      exact SourceCurrentConjunctionRequirementPullSoundness.run_common annotation ran semantic costs fields
        values.1 closed.1 (fun job member => ⟨values.2 job member, closed.2 job member⟩)
        holds ambient symbol terms part common

/-- An allocated original class retains a strictly smaller witness through its actual force. -/
theorem force_class_witness (annotation : Guard → Prop) {p h handle : Nat} {before after : Cells}
    {forests : List (List Node)} {paths : Class} {nodes : List Node}
    (found : SourceCurrentConjunctionRequirementCells.lookup handle before =
      some (.pending (SourceCurrentConjunctionRequirementPull.start forests paths)))
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before = .done nodes after)
    (semantic : SemanticReady before.physical.heap) (costs : CostHeap before.physical.heap)
    (fields : AnnotationHeap annotation before.physical.heap)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before.physical.heap forests)
    (nonempty : forests ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ forest ∈ forests, All₂ (meaning holds ambient) forest terms)
    (active : Nontrivial paths) (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, Accepts (meaning holds ambient) nodes part ∧
      part.height < (Term.node symbol terms).height := by
  have ran := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
  exact SourceCurrentConjunctionRequirementPullSoundness.classConjunction_witness annotation forests paths
    ran semantic costs fields inputs nonempty holds ambient symbol terms original active satisfied

end MicroCFTA.SourceCurrentConjunctionRequirementCellsSoundness
