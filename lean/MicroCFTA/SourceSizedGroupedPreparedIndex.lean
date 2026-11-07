import MicroCFTA.SourceSizedGroupedMinimumIndex
import MicroCFTA.SourceSizedGroupedTableIndex
import MicroCFTA.SourceSizedGroupedCurrent

/-!
# Prepared count and selector observations

The actual computed minimum supplies the table gate. Each query constructs
its finite source-combinator unfolding with a bound from the requested size.
The resulting count and guarded selector retain the checked class order.
No caller supplies gate correctness, output uniqueness, or evaluation fuel.

These are observations of the direct source field equations. Sparse storage,
lazy infinite series, native sharing and the cached bottom-up inverse remain
separate. No complete public API contract is changed here.
-/
namespace MicroCFTA.SourceSizedGroupedPreparedIndex
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Actual preparation and its computed minimum discharge the internal gate condition. -/
theorem missing_empty (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output) :
    SourceSizedGroupedTableIndex.MissingEmpty
      (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) :=
  SourceSizedGroupedMinimumIndex.known_false_empty original root output success

/-- Read the prepared source count field with its actual computed minimum gate. -/
def countAt (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (key : List State) : Nat :=
  SourceSizedGroupedTableIndex.countAt
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) size key

/-- Read the prepared source selector after its class-count guard. -/
def selectAt (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size rank : Nat) (key : List State) : Option (Term Symbol) :=
  SourceSizedGroupedTableIndex.selectAt
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) size rank key

/-- The finite source count is the exact prepared class length. -/
theorem countAt_eq (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (key : List State) :
    countAt original root output success size key =
      (SourceSizedGroupedClasses.classes (lookup output) size key).length :=
  SourceSizedGroupedTableIndex.countAt_eq _ _ (missing_empty original root output success) size key

/-- The finite source selector has the exact class position at every natural rank. -/
theorem selectAt_eq (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size rank : Nat) (key : List State) :
    selectAt original root output success size rank key =
      (SourceSizedGroupedClasses.classes (lookup output) size key)[rank]? :=
  SourceSizedGroupedTableIndex.selectAt_eq _ _ (missing_empty original root output success) size rank key

/-- The source count guard rejects exactly the ranks outside its class. -/
theorem selectAt_none_iff (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size rank : Nat) (key : List State) :
    selectAt original root output success size rank key = none ↔
      countAt original root output success size key ≤ rank :=
  SourceSizedGroupedTableIndex.selectAt_none_iff _ _ (missing_empty original root output success) size rank key

/-- Source selection covers exactly the prepared graph language at the requested node count. -/
theorem selectAt_exists_iff (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (key : List State) (term : Term Symbol) :
    (∃ rank, selectAt original root output success size rank key = some term) ↔
      Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) key term ∧ nodeSize term = size := by
  simp only [selectAt_eq]
  rw [← List.mem_iff_getElem?]
  exact SourceSizedGroupedClasses.mem_classes_iff (lookup output)
    (SourceSizedConjunctionSharing.preparation_facts original root output success) size key term

/-- The scoped actual source gate makes different class ranks select different terms. -/
theorem selectAt_rank_unique
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size first second : Nat) (key : List State) (term : Term Symbol)
    (left : selectAt (SourceSizedScopedTrimInventory.trimmedTable table root)
      root output success size first key = some term)
    (right : selectAt (SourceSizedScopedTrimInventory.trimmedTable table root)
      root output success size second key = some term) : first = second := by
  rw [selectAt_eq] at left right
  have unique := SourceSizedGroupedUnique.prepared_classes_nodup table root validated passed output success size key
  exact unique.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp left).1 (left.trans right.symm)

open SourceGuards SourceObservations SourceSymbolicIndex

/-- Actual prepared root selection covers the current ORIGINAL constraint language without normalization premises. -/
theorem root_selection [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size : Nat) (term : Term (Label Formula)) :
    (∃ rank, selectAt (SourceSizedScopedTrimInventory.trimmedTable table root)
      root output success size rank [root] = some term) ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term ∧ nodeSize term = size :=
  (selectAt_exists_iff (SourceSizedScopedTrimInventory.trimmedTable table root)
    root output success size [root] term).trans
      (and_congr (SourceSizedGroupedCurrent.prepared_root_language
        formulas solver table root validated output success term) Iff.rfl)

end MicroCFTA.SourceSizedGroupedPreparedIndex
