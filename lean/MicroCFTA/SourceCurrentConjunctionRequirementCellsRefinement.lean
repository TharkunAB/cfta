import MicroCFTA.SourceCurrentConjunctionRequirementCellsSoundness
import MicroCFTA.SourceCurrentConjunctionRequirementCellsFrame
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Original descriptor claims in shared cells

The origin list records the literal descriptor allocated at each handle.
The current cell preserves every common-term claim of that descriptor.
Actual allocation extends both lists. Successful forcing preserves their
alignment and claims. This component does not assert semantic refinement
after a failed force or supply origins for an arbitrary final table.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsRefinement
open Language
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementCells (lookup force Outcome)
open SourceCurrentConjunctionRequirementCellsSoundness (CommonCell)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- A current cell preserves each accepted common-term claim of its original descriptor. -/
def Refines (original current : Cell) : Prop :=
  ∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol),
    CommonCell holds ambient symbol terms part original → CommonCell holds ambient symbol terms part current

/-- Every original descriptor retains its exact current handle and semantic claims. -/
structure Invariant (origins : List Cell) (before : Cells) : Prop where
  length : origins.length = before.cells.length
  cells : ∀ handle original current, origins[handle]? = some original →
    lookup handle before = some current → Refines original current

/-- A newly allocated literal descriptor preserves its own common-term claims. -/
theorem Refines.refl (cell : Cell) : Refines cell cell := by
  intro holds ambient symbol terms part common
  exact common

/-- The actual empty cell heap has the empty origin list. -/
theorem initial (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Invariant [] (SourceCurrentConjunctionRequirementCells.initial before) := by
  refine ⟨rfl, ?_⟩
  intro handle original current found _
  cases handle <;> cases found

/-- Actual allocation appends the same descriptor to the immutable origin list. -/
theorem allocate (cell : Cell) (before : Cells) (origins : List Cell) (refined : Invariant origins before) :
    Invariant (origins ++ [cell]) (SourceCurrentConjunctionRequirementCells.allocate cell before).2 := by
  refine ⟨?_, ?_⟩
  · simp only [SourceCurrentConjunctionRequirementCells.allocate, List.length_append,
      List.length_singleton, refined.length]
  · intro handle original current originFound currentFound
    by_cases old : handle < origins.length
    · have originalFound : origins[handle]? = some original := by
        simpa only [List.getElem?_append_left old] using originFound
      have inside : handle < before.cells.length := by simpa only [refined.length] using old
      have prior : lookup handle before = some current := by
        change before.cells[handle]? = some current
        change (before.cells ++ [cell])[handle]? = some current at currentFound
        simpa only [List.getElem?_append_left inside] using currentFound
      exact refined.cells handle original current originalFound prior
    · have inside := (List.getElem?_eq_some_iff.mp originFound).1
      have atEnd : handle = origins.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      subst handle
      have originalSame : cell = original := by simpa using originFound
      have present := SourceCurrentConjunctionRequirementCells.lookup_allocate cell before
      change lookup before.cells.length (SourceCurrentConjunctionRequirementCells.allocate cell before).2 =
        some cell at present
      rw [← refined.length] at present
      have currentSame : current = cell := Option.some.inj (currentFound.symm.trans present)
      rw [← originalSame, currentSame]
      exact Refines.refl cell

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A successful actual force preserves every allocated descriptor's claims at the same handle. -/
theorem force_success {p h target : Nat} {before after : Cells} {nodes : List Node} {origins : List Cell}
    (actual : force p h target before = .done nodes after) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (refined : Invariant origins before) : Invariant origins after := by
  have length := SourceCurrentConjunctionRequirementCellsFrame.force_length p h target before
  rw [actual] at length
  change after.cells.length = before.cells.length at length
  refine ⟨refined.length.trans length.symm, ?_⟩
  intro handle original current originFound currentFound
  by_cases selected : handle = target
  · subst handle
    have inside : target < before.cells.length := by
      rw [← refined.length]
      exact (List.getElem?_eq_some_iff.mp originFound).1
    have prior : lookup target before = some before.cells[target] := List.getElem?_eq_getElem inside
    have preserved := refined.cells target original before.cells[target] originFound prior
    have published := SourceCurrentConjunctionRequirementPublication.force_done p h target before after nodes actual
    have currentSame : current = .done nodes := Option.some.inj (currentFound.symm.trans published)
    rw [currentSame]
    intro holds ambient symbol terms part common
    exact SourceCurrentConjunctionRequirementCellsSoundness.force_common
      (SourceCurrentConjunctionEquality.FieldAvailable before.physical.equality) prior actual
      ready.semantic ready.costs ready.fields (values target _ prior) (closed target _ prior)
      holds ambient symbol terms part (preserved holds ambient symbol terms part common)
  · have retained := SourceCurrentConjunctionRequirementCellsEffects.force_other p h target before handle selected
    rw [actual] at retained
    change lookup handle after = lookup handle before at retained
    exact refined.cells handle original current originFound (retained.symm.trans currentFound)

end MicroCFTA.SourceCurrentConjunctionRequirementCellsRefinement
