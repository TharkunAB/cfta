import MicroCFTA.SourceCurrentConjunctionScanClassPass

#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPass.from_scan
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPass.finite
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.Reduction
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.Reads
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.Ranges
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.Receipt
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.from_scan
#check @MicroCFTA.SourceCurrentConjunctionScanClassPass.finite

namespace MicroCFTA.SourceCurrentConjunctionScanClassPassProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentConjunctionScanClassPass
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
local notation "coldFourth" => SourceCurrentEmptinessMemo.empty
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- A stopped raw graph has exact erasure and performs no class-pass merge request.
theorem stopped_layout {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {paths : Class}
    (actual : Reduction budget records values before fourth memo (some paths) results after savedFourth saved) :
    results = EqualityLeafProjectionRuntimeEmpty.erase values ∧ saved = memo := by
  cases actual with
  | stopped _ => exact ⟨rfl, rfl⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
variable (values : List (Value Symbol Guard)) (before : Checked width)
variable (ready : Ready before) (admitted : At formulas solver inventory before)
variable (available : Values before.native.machine.heap values)
variable (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
variable (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
  EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
include inventory ready admitted available proper fields

-- Cold result and fourth tables derive their own initial invariants; global tables can start warm.
theorem cold_local
    (ranges : Ranges budget records values before coldFourth cold) (memos : Memos)
    (valid : Valid before.native.machine.heap memos) :
    ∃ outcome results after savedFourth saved next final,
      ∃ actual : Reduction budget records values before coldFourth cold outcome results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next records values results before after coldFourth savedFourth cold saved outcome final ∧
        results.length = values.length ∧ Valid after.native.machine.heap final := by
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ := finite
    formulas solver inventory budget records values before coldFourth cold ready admitted available proper fields
    (SourceCurrentEmptinessMemo.empty_correct formulas solver _) (SourceCurrentMemoMergeEffects.stored_empty _)
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty _ ambient) ranges memos valid
  exact ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt, receipt.length, receipt.globals⟩

-- An accepted forest that satisfies every original class cannot take the stopped result.
theorem satisfying_success
    (fourth : Fourth) (memo : Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget records values before fourth memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)
    (satisfied : ∀ record ∈ records, ClassSat (.node symbol terms) record.paths) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget records values before fourth memo none results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next records values results before after fourth savedFourth memo saved none final ∧
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms := by
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ := finite
    formulas solver inventory budget records values before fourth memo ready admitted available proper fields
    correct stored covered ranges memos valid
  cases outcome with
  | none =>
      exact ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt,
        ((receipt.language ambient symbol terms).2 satisfied).mpr accepted⟩
  | some paths =>
      have stopped := receipt.rejected paths rfl
      obtain ⟨record, member, same⟩ := List.mem_map.mp stopped.1
      exact False.elim (stopped.2 ambient symbol terms accepted (same ▸ satisfied record member))

-- Every complete local return admits another generated query from the same warm state.
theorem local_then_query
    (fourth : Fourth) (memo : Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget records values before fourth memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (queryRanges : ∀ outcome results after savedFourth saved,
      Reduction budget records values before fourth memo outcome results after savedFourth saved →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after) :
    ∃ outcome results after savedFourth saved next final queryInventory result checked,
      Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory left right after result checked final ∧
      SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Correct formulas solver checked.native.machine.heap savedFourth := by
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, actual, _, receipt⟩ := finite
    formulas solver inventory budget records values before fourth memo ready admitted available proper fields
    correct stored covered ranges memos valid
  obtain ⟨queryInventory, result, checked, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver next left right after receipt.ready receipt.admitted
    (receipt.effects.keeps.available left leftAvailable) (receipt.effects.keeps.available right rightAvailable)
    leftClosed rightClosed (queryRanges outcome results after savedFourth saved actual) final receipt.globals
  exact ⟨outcome, results, after, savedFourth, saved, next, final, queryInventory, result, checked, receipt, query,
    receipt.stored.grows query.effects.keeps,
    SourceCurrentEmptinessMemo.grows formulas solver query.effects.keeps savedFourth receipt.correct⟩

end MicroCFTA.SourceCurrentConjunctionScanClassPassProbes

#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.stopped_layout
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.cold_local
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.satisfying_success
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.local_then_query
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.stopped_layout
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.cold_local
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.satisfying_success
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassProbes.local_then_query
