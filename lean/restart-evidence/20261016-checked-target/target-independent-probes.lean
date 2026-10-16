import MicroCFTA.SourceCurrentAllocatedTargetComplete

#print axioms MicroCFTA.SourceCurrentAllocatedTargetComplete.Fold.verified
#print axioms MicroCFTA.SourceCurrentAllocatedTargetComplete.fold_complete
#print axioms MicroCFTA.SourceCurrentAllocatedTargetComplete.target_complete
#print axioms MicroCFTA.SourceCurrentAllocatedTargetComplete.Target.verified
#print axioms MicroCFTA.SourceCurrentAllocatedTargetComplete.Receipt.fourth_correct
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetComplete.Fold.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetComplete.fold_complete
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetComplete.target_complete
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetComplete.Target.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetComplete.Receipt.fourth_correct

namespace MicroCFTA.AllocatedTargetIndependentProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentAllocatedTargetComplete
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "S" => SourceObservations.Label FullSyntax.Formula
local notation "G" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo S G
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Ranges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat} [DecidableEq S] [DecidableEq (EdgeKey S G)]

-- Two paths complete from a warm state with the same initial merge table.
theorem two_path_warm
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value S G)) (seed head : List Int)
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ [seed, head], Domain path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values [seed, head] before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Target values [seed, head] before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values [seed, head] before memo result after saved memos final :=
  target_complete formulas solver inventory values [seed, head] before memo ready admitted available domains
    stored covered ranges memos valid

-- Three paths complete in the literal head, tail, checked-intersection schedule.
theorem three_path_warm
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value S G)) (seed head last : List Int)
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ [seed, head, last], Domain path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values [seed, head, last] before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Target values [seed, head, last] before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values [seed, head, last] before memo result after saved memos final :=
  target_complete formulas solver inventory values [seed, head, last] before memo ready admitted available domains
    stored covered ranges memos valid

-- Any existing raw target receives the same physical and semantic receipt.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value S G)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value S G}
    (actual : Target values paths before memo result after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ paths, Domain path values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next final, TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final :=
  SourceCurrentAllocatedTargetComplete.Target.verified formulas solver inventory actual ready admitted available domains
    stored covered ranges memos valid

-- The empty raw target has no state or merge-table effects.
example {values : List (Value S G)} {before after : Checked width} {memo saved : Memo} {result : Value S G}
    (actual : Target values [] before memo result after saved) : result = .empty ∧ after = before ∧ saved = memo := by
  cases actual
  exact ⟨rfl, rfl, rfl⟩

-- Its reads retain the identical global bundle.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value S G)} {before : Checked width} {memo : Memo} {memos final : Memos}
    (reads : TargetReads formulas solver (Target.nil (values := values) (before := before) (memo := memo)) memos final) :
    final = memos := by
  cases reads
  rfl

-- The fourth table retains its old input records and semantic laws through actual target growth.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value S G)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value S G} {memos final : Memos}
    (receipt : Receipt formulas solver inventory values paths before memo result after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth := receipt.fourth_correct fourth correct

-- Two generated queries expose both actual entry heaps and both finite root inventories.
-- The shape is head ∩ (last ∩ seed), as for a three-path right fold.
theorem two_generated_queries
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (head last seed : Value S G) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (headAvailable : Available before.native.machine.heap head)
    (lastAvailable : Available before.native.machine.heap last) (seedAvailable : Available before.native.machine.heap seed)
    (headClosed : head.free = []) (lastClosed : last.free = []) (seedClosed : seed.free = [])
    (firstRanges : Ranges (.code (requestNode emptyDomain last seed)) before)
    (secondRanges : ∀ inner middle, SourceCurrentAllocatedTargetQuery.Step last seed before inner middle →
      Ranges (.code (requestNode emptyDomain head inner)) middle)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ firstInventory inner middle secondInventory result after,
      firstInventory.source = before.native.machine.heap ∧ firstInventory.roots = inventory.roots ++ [last, seed] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver firstInventory last seed before inner middle memos ∧
      secondInventory.source = middle.native.machine.heap ∧ secondInventory.roots = firstInventory.roots ++ [head, inner] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver secondInventory head inner middle result after memos ∧
      (∀ ambient term, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        meaning (SourceEqualityPCSGuard.holds formulas solver) ambient head term ∧
        (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient last term ∧
          meaning (SourceEqualityPCSGuard.holds formulas solver) ambient seed term)) := by
  obtain ⟨firstInventory, inner, middle, sourceOne, rootsOne, first⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver inventory last seed before ready admitted lastAvailable seedAvailable lastClosed seedClosed firstRanges memos valid
  obtain ⟨secondInventory, result, after, sourceTwo, rootsTwo, second⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver firstInventory head inner middle first.ready first.admitted
    (first.effects.keeps.available head headAvailable) first.available headClosed first.closed
    (secondRanges inner middle first.actual) memos first.globals
  refine ⟨firstInventory, inner, middle, secondInventory, result, after, sourceOne, rootsOne, first,
    sourceTwo, rootsTwo, second, ?_⟩
  intro ambient term
  exact (second.meaning ambient term).trans (and_congr Iff.rfl (first.meaning ambient term))
end MicroCFTA.AllocatedTargetIndependentProbes

#print axioms MicroCFTA.AllocatedTargetIndependentProbes.two_path_warm
#print axioms MicroCFTA.AllocatedTargetIndependentProbes.three_path_warm
#print axioms MicroCFTA.AllocatedTargetIndependentProbes.two_generated_queries
