import MicroCFTA.SourceSizedGroupedBottomUp

/-!
# Prepared bottom-up rank and selector inverses

The actual prepared minimum supplies the state gate. Preparation supplies
valid shared rows. The actual scoped unambiguity check supplies distinct
classes. These facts discharge the internal bottom-up worker conditions.

The rank operation uses the source candidate, cached-prefix and last-write
value equations. It does not search materialized classes. Native lazy indexes,
finite map storage, cache realization and the outer dispatcher remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedPreparedRank
open Language RecursiveSize SizedRank SourceSizedDecided SourceSizedFiniteKeys

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Run the source bottom-up rank with its actual computed prepared minimum gate. -/
def rankAt (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) : Option Position :=
  SourceSizedGroupedBottomUp.positionsOf
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) term key

/-- Every returned prepared source rank replays its input term at the exact class position. -/
theorem rankAt_replay (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) (position : Position)
    (found : rankAt original root output success key term = some position) :
    (SourceSizedGroupedClasses.classes (lookup output) position.size key)[position.rank]? = some term :=
  SourceSizedGroupedBottomUp.positionsOf_replay _ _
    (SourceSizedGroupedPreparedIndex.missing_empty original root output success)
    (SourceSizedConjunctionSharing.preparation_facts original root output success) term key position found

/-- Prepared source rank existence is exactly prepared graph acceptance. -/
theorem rankAt_exists_iff (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) :
    (∃ position, rankAt original root output success key term = some position) ↔
      Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) key term :=
  SourceSizedGroupedBottomUp.positionsOf_accepts _ _
    (SourceSizedGroupedPreparedIndex.missing_empty original root output success)
    (SourceSizedConjunctionSharing.preparation_facts original root output success) term key

/-- The returned source size is the actual node count of the ranked term. -/
theorem rankAt_size (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) (position : Position)
    (found : rankAt original root output success key term = some position) :
    nodeSize term = position.size :=
  ((SourceSizedGroupedClasses.mem_classes_iff (lookup output)
    (SourceSizedConjunctionSharing.preparation_facts original root output success)
    position.size key term).mp
      (List.mem_of_getElem? (rankAt_replay original root output success key term position found))).2

/-- Actual scoped unambiguity and preparation give both rank and selector inverse directions. -/
theorem rankAt_select_iff
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (key : List State) (term : Term Symbol) (size rank : Nat) :
    rankAt (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key term =
        some ⟨size, rank⟩ ↔
      SourceSizedGroupedPreparedIndex.selectAt
        (SourceSizedScopedTrimInventory.trimmedTable table root) root output success size rank key = some term :=
  SourceSizedGroupedBottomUp.positionsOf_select_iff _ _
    (SourceSizedGroupedPreparedIndex.missing_empty
      (SourceSizedScopedTrimInventory.trimmedTable table root) root output success)
    (SourceSizedConjunctionSharing.preparation_facts
      (SourceSizedScopedTrimInventory.trimmedTable table root) root output success)
    (SourceSizedGroupedUnique.prepared_classes_nodup table root validated passed output success)
    term key ⟨size, rank⟩

open SourceGuards SourceObservations SourceSymbolicIndex

/-- Original root rank existence uses current raw constraint acceptance without normalization premises. -/
theorem root_rank_iff [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (term : Term (Label Formula)) :
    (∃ position, rankAt (SourceSizedScopedTrimInventory.trimmedTable table root)
      root output success [root] term = some position) ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term :=
  (rankAt_exists_iff (SourceSizedScopedTrimInventory.trimmedTable table root)
    root output success [root] term).trans
      (SourceSizedGroupedCurrent.prepared_root_language formulas solver table root validated output success term)

end MicroCFTA.SourceSizedGroupedPreparedRank
