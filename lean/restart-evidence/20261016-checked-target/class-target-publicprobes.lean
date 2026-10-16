import MicroCFTA.SourceCurrentAllocatedClassTarget

#print axioms MicroCFTA.SourceCurrentAllocatedClassTarget.receipt_included
#print axioms MicroCFTA.SourceCurrentAllocatedClassTarget.finite
#print axioms MicroCFTA.SourceCurrentAllocatedClassTarget.actual_verified
#check @MicroCFTA.SourceCurrentAllocatedClassTarget.SelectedIncludes
#check @MicroCFTA.SourceCurrentAllocatedClassTarget.receipt_included
#check @MicroCFTA.SourceCurrentAllocatedClassTarget.finite
#check @MicroCFTA.SourceCurrentAllocatedClassTarget.actual_verified

namespace MicroCFTA.SourceCurrentAllocatedClassTargetProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityClassTarget (operandPaths)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentAllocatedClassTarget
open SourceCurrentMemoMergeEffects (Stored stored_empty)
open SourceCurrentMemoMergeLanguage (CacheCovers cache_covers_empty)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- An empty merge table supplies its own cache invariants for an actual finite class target.
theorem cold_class_target
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (ranges : TargetRanges values (operandPaths record.paths path) before cold)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final,
      ∃ actual : Target values (operandPaths record.paths path) before cold result after saved,
        SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
        SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values
          (operandPaths record.paths path) before cold result after saved memos final ∧
        result.free = [] ∧ SelectedIncludes formulas solver record values path result := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt, selected⟩ := finite
    formulas solver inventory record coherent active path member values before cold ready admitted available domains
    (stored_empty _) (fun ambient => cache_covers_empty _ ambient) ranges memos valid
  exact ⟨result, after, saved, next, final, actual, reads, receipt, receipt.closed, selected⟩

-- Historical target language does not require the current inventory to equal its historical inventory.
theorem historical_target
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : Path} {result : Value Symbol Guard} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver inventory values
      (operandPaths record.paths path) before memo result after saved memos final)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths) (member : path ∈ record.paths)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps after.native.machine.heap heap) :
    Available heap result ∧ result.free = [] ∧ SelectedIncludes formulas solver record values path result :=
  ⟨keeps.available result receipt.available, receipt.closed, receipt_included receipt coherent active member⟩

-- A checked class target followed by an actual leaf intersection derives narrowing and conditional retention.
theorem class_target_then_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values (operandPaths record.paths path) before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (input : Value Symbol Guard) (inputAvailable : Available before.native.machine.heap input) (inputClosed : input.free = [])
    (leafRanges : ∀ target middle saved,
      Target values (operandPaths record.paths path) before memo target middle saved →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) middle) :
    ∃ target middle saved next current finalInventory result after,
      (∃ actual : Target values (operandPaths record.paths path) before memo target middle saved,
        SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos current) ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values
        (operandPaths record.paths path) before memo target middle saved memos current ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver finalInventory target input middle result after current ∧
      (∀ ambient part, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part →
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input part) ∧
      (∀ ambient symbol terms part,
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        ClassSat (.node symbol terms) record.paths → (Term.node symbol terms).atPath path = some part →
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input part →
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part) := by
  obtain ⟨target, middle, saved, next, current, actual, reads, receipt, selected⟩ := finite
    formulas solver inventory record coherent active path member values before memo ready admitted available domains
    stored covered ranges memos valid
  obtain ⟨finalInventory, result, after, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver next target input middle receipt.ready receipt.admitted receipt.available
    (receipt.effects.keeps.available input inputAvailable) receipt.closed inputClosed (leafRanges target middle saved actual)
    current receipt.globals.valid
  refine ⟨target, middle, saved, next, current, finalInventory, result, after,
    ⟨actual, reads⟩, receipt, query, ?_, ?_⟩
  · intro ambient part accepted
    exact ((query.meaning ambient part).mp accepted).2
  · intro ambient symbol terms part accepted satisfied atPath inputAccepted
    exact (query.meaning ambient part).mpr ⟨selected ambient symbol terms part accepted satisfied atPath, inputAccepted⟩

end MicroCFTA.SourceCurrentAllocatedClassTargetProbes

#print axioms MicroCFTA.SourceCurrentAllocatedClassTargetProbes.cold_class_target
#print axioms MicroCFTA.SourceCurrentAllocatedClassTargetProbes.historical_target
#print axioms MicroCFTA.SourceCurrentAllocatedClassTargetProbes.class_target_then_query
#check @MicroCFTA.SourceCurrentAllocatedClassTargetProbes.cold_class_target
#check @MicroCFTA.SourceCurrentAllocatedClassTargetProbes.historical_target
#check @MicroCFTA.SourceCurrentAllocatedClassTargetProbes.class_target_then_query
