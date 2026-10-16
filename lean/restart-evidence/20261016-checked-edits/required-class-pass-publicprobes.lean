import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPass.selected_domains
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPass.satisfied_required
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPass.verified
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPass.finite
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPass.Receipt.fourth_correct
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.Receipt
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.selected_domains
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.satisfied_required
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.verified
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.finite
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPass.Receipt.fourth_correct

namespace MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassPass (Pass PassReads Ranges)
open SourceCurrentConjunctionRequiredClassPass
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
variable {before prepared : Checked width}
variable (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
variable (records : List SourceEqualityClassOrder.Record)
variable (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
variable (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
variable (active : ∀ record ∈ records, Nontrivial record.paths)
include inventory required selectedEq coherent active

-- A current required return constructs the complete pass and derives its own cold fourth-memo invariant.
theorem required_cold_pass
    (ranges : Ranges records values prepared cold) (memos : Memos) (valid : Valid prepared.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Pass records values prepared cold results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records selected originals values before prepared cold results after saved memos final ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap SourceCurrentEmptinessMemo.empty ∧
      final.query = memos.query := by
  obtain ⟨results, after, saved, next, final, actual, reads, checked⟩ := finite formulas solver inventory required records
    selectedEq coherent active cold (SourceCurrentMemoMergeEffects.stored_empty _)
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty _ ambient) ranges memos valid
  exact ⟨results, after, saved, next, final, actual, reads, checked,
    checked.fourth_correct _ (SourceCurrentEmptinessMemo.empty_correct formulas solver _), checked.pass.globals.query⟩

-- Selected class satisfaction removes the required filter premise from exact language retention.
theorem class_satisfying_original_kept
    (memo : Memo) (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges records values prepared memo) (memos : Memos) (valid : Valid prepared.native.machine.heap memos)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : ∀ paths ∈ selected, ClassSat (.node symbol terms) paths)
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) originals terms) :
    ∃ results after saved next final, ∃ actual : Pass records values prepared memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records selected originals values before prepared memo results after saved memos final ∧
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ∧
      SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms := by
  obtain ⟨results, after, saved, next, final, actual, reads, checked⟩ := finite formulas solver inventory required records
    selectedEq coherent active memo stored covered ranges memos valid
  have kept := ((checked.language ambient symbol terms).2 satisfied).mpr accepted
  exact ⟨results, after, saved, next, final, actual, reads, checked, kept,
    ((checked.language ambient symbol terms).1 kept).2⟩

-- The computed pass inventory supports the next generated query without a new model or admission premise.
theorem pass_then_query
    (memo : Memo) (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges records values prepared memo) (memos : Memos) (valid : Valid prepared.native.machine.heap memos)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (queryRanges : ∀ results after saved, Pass records values prepared memo results after saved →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after) :
    ∃ results after saved next final queryInventory result checked,
      Receipt formulas solver next records selected originals values before prepared memo results after saved memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory left right after result checked final ∧
      SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap saved ∧
      (∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved) := by
  obtain ⟨results, after, saved, next, final, actual, _, receipt⟩ := finite formulas solver inventory required records
    selectedEq coherent active memo stored covered ranges memos valid
  obtain ⟨queryInventory, result, checked, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver next left right after receipt.pass.ready receipt.pass.admitted
    (receipt.effects.keeps.available left leftAvailable) (receipt.effects.keeps.available right rightAvailable)
    leftClosed rightClosed (queryRanges results after saved actual) final receipt.pass.globals.valid
  exact ⟨results, after, saved, next, final, queryInventory, result, checked, receipt, query,
    receipt.pass.stored.grows query.effects.keeps, receipt.pass.covered⟩

end MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes

#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.required_cold_pass
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.class_satisfying_original_kept
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.pass_then_query
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.required_cold_pass
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.class_satisfying_original_kept
#check @MicroCFTA.SourceCurrentConjunctionRequiredClassPassProbes.pass_then_query
