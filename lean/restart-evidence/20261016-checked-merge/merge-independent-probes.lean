import MicroCFTA.SourceCurrentAllocatedMergeOperand

#print axioms MicroCFTA.SourceCurrentAllocatedMerge.top_true
#print axioms MicroCFTA.SourceCurrentAllocatedMerge.literalClear_true
#print axioms MicroCFTA.SourceCurrentAllocatedMerge.normalized_clear_boundary
#print axioms MicroCFTA.SourceCurrentAllocatedMerge.verified
#print axioms MicroCFTA.SourceCurrentAllocatedMerge.finite
#print axioms MicroCFTA.SourceCurrentAllocatedMerge.source_finite
#print axioms MicroCFTA.SourceCurrentAllocatedMergeOperand.complete
#print axioms MicroCFTA.SourceCurrentAllocatedMergeOperand.of_required
#check @MicroCFTA.SourceCurrentAllocatedMerge.literalClear
#check @MicroCFTA.SourceCurrentAllocatedMerge.Merge
#check @MicroCFTA.SourceCurrentAllocatedMerge.Receipt
#check @MicroCFTA.SourceCurrentAllocatedMerge.top_true
#check @MicroCFTA.SourceCurrentAllocatedMerge.literalClear_true
#check @MicroCFTA.SourceCurrentAllocatedMerge.normalized_clear_boundary
#check @MicroCFTA.SourceCurrentAllocatedMerge.verified
#check @MicroCFTA.SourceCurrentAllocatedMerge.finite
#check @MicroCFTA.SourceCurrentAllocatedMerge.source_finite
#check @MicroCFTA.SourceCurrentAllocatedMergeOperand.Receipt
#check @MicroCFTA.SourceCurrentAllocatedMergeOperand.complete
#check @MicroCFTA.SourceCurrentAllocatedMergeOperand.of_required

namespace MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentMemoMergeEffects (Stored stored_empty)
open SourceCurrentMemoMergeLanguage (CacheCovers cache_covers_empty)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Cold merge completion derives its physical and language cache invariants.
theorem cold_merge
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (input : Value Symbol Guard) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Available before.native.machine.heap input) (closed : input.free = [])
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ output after saved final,
      SourceCurrentAllocatedMerge.Receipt formulas solver inventory literalClear input before cold output after saved memos final ∧
      output.free = [] ∧ SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap := by
  obtain ⟨output, after, saved, final, receipt⟩ := SourceCurrentAllocatedMerge.source_finite
    formulas solver inventory input before cold ready admitted (stored_empty _) (fun ambient => cache_covers_empty _ ambient)
    available memos valid
  exact ⟨output, after, saved, final, receipt, receipt.closed closed, receipt.ready.good.fields⟩

-- A present merge key returns in the identical checked state and has a literal no-read global receipt.
theorem warm_hit
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (input : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (available : Available before.native.machine.heap input) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, SourceCurrentAllocatedMerge.Receipt formulas solver inventory literalClear
      input before memo entry.result before memo memos final ∧
      SourceCurrentMemoMergeQueryMemos.CallReads literalClear top input before.native.machine.heap memo
        entry.result before.native.machine.heap memo memos memos := by
  have actual : SourceCurrentAllocatedMerge.Merge literalClear input before memo entry.result before memo := by
    have entered := SourceCurrentAllocatedMerge.Merge.done (before := before)
      (SourceCurrentAllocatedMergeGraph.Call.hit (clear := literalClear) (before := physical before) found)
    simpa only [SourceCurrentAllocatedConjunctionMemo.advance_self] using entered
  obtain ⟨final, receipt⟩ := SourceCurrentAllocatedMerge.verified formulas solver inventory literalClear
    (SourceCurrentAllocatedMerge.literalClear_true formulas solver) actual ready admitted stored covered available memos valid
  exact ⟨final, receipt, .hit found memos⟩

-- Required paths construct a cold merged operand without supplied future Fields or target language laws.
theorem required_operand
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before after)
    (path : Path) (member : path ∈ selected.flatten) (memos : Memos) (valid : Valid after.native.machine.heap memos) :
    ∃ output reached saved final,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory (path.map Int.ofNat)
        values after cold output reached saved memos final ∧ output.free = [] ∧
      At formulas solver inventory reached ∧ Values reached.native.machine.heap values := by
  obtain ⟨output, reached, saved, final, receipt⟩ := SourceCurrentAllocatedMergeOperand.of_required
    formulas solver inventory required path member cold (stored_empty _) (fun ambient => cache_covers_empty _ ambient) memos valid
  exact ⟨output, reached, saved, final, receipt, receipt.closed, receipt.admitted, receipt.originals⟩

-- The actual merged result can be admitted by the next generated query with only its reached WordRanges.
theorem operand_then_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (other : Value Symbol Guard) (otherAvailable : Available before.native.machine.heap other) (otherClosed : other.free = [])
    (ranges : ∀ output middle saved final,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output middle saved memos final →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain output other)) middle) :
    ∃ output middle saved final next fuel result after,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output middle saved memos final ∧
      next.source = middle.native.machine.heap ∧
      SourceCurrentAllocatedNativeCoveredQuery.Receipt next.source formulas solver
        (next.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel output other middle result after ∧
      At formulas solver next after ∧ result.free = [] ∧
      (path ≠ [] → ∀ ambient symbol terms part,
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        SymbolicSignedPaths.lookup (.node symbol terms) path = some part →
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient other part →
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part) := by
  obtain ⟨output, middle, saved, final, operand⟩ := SourceCurrentAllocatedMergeOperand.complete
    formulas solver inventory path values before memo ready admitted available domain stored covered memos valid
  obtain ⟨next, fuel, result, after, source, _, query, finalAt⟩ := SourceCurrentAllocatedNativeInventoryState.query_complete
    inventory formulas solver middle operand.ready.good operand.admitted operand.ready.scopedCache
    operand.ready.semantic operand.ready.idle output other operand.available
    (operand.effects.keeps.available other otherAvailable) operand.closed otherClosed (ranges output middle saved final operand)
  refine ⟨output, middle, saved, final, next, fuel, result, after, operand, source, query, finalAt, query.closed, ?_⟩
  intro proper ambient symbol terms part accepted selected acceptedOther
  exact (query.meaning ambient part).mpr ⟨operand.included proper ambient symbol terms part accepted selected, acceptedOther⟩

end MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes

#print axioms MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.cold_merge
#print axioms MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.warm_hit
#print axioms MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.required_operand
#print axioms MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.operand_then_query
#check @MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.cold_merge
#check @MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.warm_hit
#check @MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.required_operand
#check @MicroCFTA.SourceCurrentAllocatedMergeIndependentProbes.operand_then_query
