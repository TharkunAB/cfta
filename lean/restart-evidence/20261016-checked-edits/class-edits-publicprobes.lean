import MicroCFTA.SourceCurrentAllocatedClassEdits

#print axioms MicroCFTA.SourceCurrentAllocatedClassEdits.verified
#print axioms MicroCFTA.SourceCurrentAllocatedClassEdits.finite
#print axioms MicroCFTA.SourceCurrentAllocatedClassEdits.Receipt.fourth_correct
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.Class
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.ClassReads
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.ClassRanges
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.Receipt
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.verified
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.finite
#check @MicroCFTA.SourceCurrentAllocatedClassEdits.Receipt.fourth_correct

namespace MicroCFTA.SourceCurrentAllocatedClassEditsProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Actual required preparation supplies every selected class domain without whole-forest closure.
theorem required_cold_class
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before prepared : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
    (record : SourceEqualityClassOrder.Record) (retained : record.paths ∈ selected)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (ranges : ClassRanges record values prepared cold)
    (memos : Memos) (valid : Valid prepared.native.machine.heap memos)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver prepared.native.machine.heap fourth) :
    ∃ results after saved next final, ∃ actual : Class record values prepared cold results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values prepared cold results after saved memos final ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth ∧
      final.query = memos.query := by
  have domains : ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
    intro path member
    exact required.paths path (List.mem_flatten.mpr ⟨record.paths, retained, member⟩)
  obtain ⟨results, after, saved, next, final, actual, reads, receipt⟩ := finite formulas solver inventory
    record coherent active values prepared cold required.ready required.admitted required.resident domains
    (SourceCurrentMemoMergeEffects.stored_empty _) (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty _ ambient)
    ranges memos valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt,
    receipt.fourth_correct fourth correct, receipt.globals.query⟩

-- The rightmost class runs first. Its actual result supplies the next class's captured forest.
theorem two_classes
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (head tail : SourceEqualityClassOrder.Record)
    (headCoherent : SourceEqualityClassOrder.Coherent head) (tailCoherent : SourceEqualityClassOrder.Coherent tail)
    (headActive : Nontrivial head.paths) (tailActive : Nontrivial tail.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (headDomains : ∀ path ∈ head.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (tailDomains : ∀ path ∈ tail.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (tailRanges : ClassRanges tail values before memo)
    (headRanges : ∀ middle reached saved, Class tail values before memo middle reached saved →
      ClassRanges head middle reached saved)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ middle reached saved next current results after finalMemo finalInventory final,
      (∃ tailActual : Class tail values before memo middle reached saved,
        ClassReads formulas solver tailActual memos current ∧
        Receipt formulas solver next tail values before memo middle reached saved memos current) ∧
      (∃ headActual : Class head middle reached saved results after finalMemo,
        ClassReads formulas solver headActual current final ∧
        Receipt formulas solver finalInventory head middle reached saved results after finalMemo current final) ∧
      (∀ path, SourceEqualityProjectionPathDomain.ForestClosed path values →
        SourceEqualityProjectionPathDomain.ForestClosed path results) ∧
      (∀ ambient symbol terms,
        (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
        (ClassSat (.node symbol terms) head.paths → ClassSat (.node symbol terms) tail.paths →
          (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))) := by
  obtain ⟨middle, reached, saved, next, current, tailActual, tailReads, first⟩ := finite formulas solver inventory
    tail tailCoherent tailActive values before memo ready admitted available tailDomains stored covered tailRanges memos valid
  have nextDomains : ∀ path ∈ head.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) middle := by
    intro path member
    exact first.domains _ (headDomains path member)
  obtain ⟨results, after, finalMemo, finalInventory, final, headActual, headReads, second⟩ := finite
    formulas solver next head headCoherent headActive middle reached saved first.ready first.admitted first.available
    nextDomains first.stored first.covered (headRanges middle reached saved tailActual) current first.globals.valid
  refine ⟨middle, reached, saved, next, current, results, after, finalMemo, finalInventory, final,
    ⟨tailActual, tailReads, first⟩, ⟨headActual, headReads, second⟩,
    (fun path domain => second.domains path (first.domains path domain)), ?_⟩
  intro ambient symbol terms
  have firstLanguage := first.language ambient symbol terms
  have secondLanguage := second.language ambient symbol terms
  exact ⟨fun accepted => firstLanguage.1 (secondLanguage.1 accepted),
    fun headSat tailSat => (secondLanguage.2 headSat).trans (firstLanguage.2 tailSat)⟩

-- The returned inventory supports a new generated query with only its reached machine checks.
theorem class_then_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : ClassRanges record values before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (queryRanges : ∀ results after saved, Class record values before memo results after saved →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after) :
    ∃ results after saved next final queryInventory result checked,
      Receipt formulas solver next record values before memo results after saved memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory left right after result checked final ∧
      SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap saved ∧
      (∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved) ∧
      final.query = memos.query := by
  obtain ⟨results, after, saved, next, final, actual, _, receipt⟩ := finite formulas solver inventory record coherent active
    values before memo ready admitted available domains stored covered ranges memos valid
  obtain ⟨queryInventory, result, checked, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver next left right after receipt.ready receipt.admitted
    (receipt.effects.keeps.available left leftAvailable) (receipt.effects.keeps.available right rightAvailable)
    leftClosed rightClosed (queryRanges results after saved actual) final receipt.globals.valid
  exact ⟨results, after, saved, next, final, queryInventory, result, checked, receipt, query,
    receipt.stored.grows query.effects.keeps, receipt.covered, receipt.globals.query⟩

end MicroCFTA.SourceCurrentAllocatedClassEditsProbes

#print axioms MicroCFTA.SourceCurrentAllocatedClassEditsProbes.required_cold_class
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditsProbes.two_classes
#print axioms MicroCFTA.SourceCurrentAllocatedClassEditsProbes.class_then_query
#check @MicroCFTA.SourceCurrentAllocatedClassEditsProbes.required_cold_class
#check @MicroCFTA.SourceCurrentAllocatedClassEditsProbes.two_classes
#check @MicroCFTA.SourceCurrentAllocatedClassEditsProbes.class_then_query
