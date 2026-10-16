import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget

/-!
# Numeric capacity at reached checked target queries

Capacity plans inspect actual earlier operands and earlier tail folds.
They contain no current query completion or returned-state invariant.
Induction on the remaining paths derives the tail range plan first.
The actual earlier tail then supplies its domain and current readiness.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalValid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Only earlier completed operand and tail prefixes select numeric capacity checks. -/
def FoldCapacity (bits : Nat) (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Checked (bits + 2) → Memo → Prop
  | [], _, _ => True
  | path :: paths, before, memo =>
      (∀ head middle current, Operand path values before memo head middle current →
        FoldCapacity bits values seed paths middle current) ∧
      (∀ head middle current tail later saved,
        Operand path values before memo head middle current → Fold values seed paths middle current tail later saved →
        Capacity bits later)

/-- Empty and singleton targets have no native intersection capacity check. -/
def TargetCapacity (bits : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) : Prop :=
  match paths with
  | [] => True
  | seed :: paths => FoldCapacity bits values seed paths before memo

/-- An actual head operand restricts the plan to its exact tail state and merge memo. -/
theorem FoldCapacity.tail {bits : Nat} {values : List (Value Symbol Guard)} {seed path : List Int}
    {paths : List (List Int)} {before middle : Checked (bits + 2)} {memo current : Memo}
    {head : Value Symbol Guard} (capacity : FoldCapacity bits values seed (path :: paths) before memo)
    (operand : Operand path values before memo head middle current) :
    FoldCapacity bits values seed paths middle current := capacity.1 _ _ _ operand

/-- The current request needs only the supply bounds at its actual earlier tail return. -/
theorem FoldCapacity.query {bits : Nat} {values : List (Value Symbol Guard)} {seed path : List Int}
    {paths : List (List Int)} {before middle later : Checked (bits + 2)} {memo current saved : Memo}
    {head tail : Value Symbol Guard} (capacity : FoldCapacity bits values seed (path :: paths) before memo)
    (operand : Operand path values before memo head middle current)
    (rest : Fold values seed paths middle current tail later saved) : Capacity bits later :=
  capacity.2 _ _ _ _ _ _ operand rest

/-- Numeric checks at earlier returns derive every native range check in the fold. -/
theorem fold_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (capacity : FoldCapacity bits values seed paths before memo) (memos : Memos)
    (valid : GlobalValid before.native.machine.heap memos) : FoldRanges values seed paths before memo := by
  induction paths generalizing inventory before memo memos with
  | nil => trivial
  | cons path paths ih =>
      refine ⟨?_, ?_⟩
      · intro head middle current operand
        obtain ⟨currentMemos, receipt, merged, native, _⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryTarget.operand formulas solver inventory operand ready admitted available
            domain physicalStored mergeStored nativeStored covered memos valid
        exact ih inventory middle current receipt.ready receipt.admitted receipt.originals receipt.stored
          merged native receipt.covered (capacity.tail operand) currentMemos receipt.globals
      · intro head middle current tail later saved operand rest
        obtain ⟨currentMemos, first, merged, native, headDomain⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryTarget.operand formulas solver inventory operand ready admitted available
            domain physicalStored mergeStored nativeStored covered memos valid
        have tailRanges := ih inventory middle current first.ready first.admitted first.originals first.stored
          merged native first.covered (capacity.tail operand) currentMemos first.globals
        obtain ⟨_next, _final, _reads, remaining, _merged, _native, tailDomain⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryTarget.fold formulas solver inventory rest first.ready first.admitted first.originals
            domain first.stored merged native first.covered tailRanges currentMemos first.globals
        exact SourceCurrentAllocatedFiniteOrdinaryCapacity.node_words bits later remaining.ready.good head tail
          (remaining.effects.keeps.available head first.available) remaining.available headDomain tailDomain
          (capacity.query operand rest)

/-- The literal target seed retains the causal numeric plan for its right fold. -/
theorem target_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (capacity : TargetCapacity bits values paths before memo) (memos : Memos)
    (valid : GlobalValid before.native.machine.heap memos) : TargetRanges values paths before memo := by
  cases paths with
  | nil => trivial
  | cons seed paths =>
      exact fold_ranges formulas solver inventory bits values seed paths before memo ready admitted
        available domain physicalStored mergeStored nativeStored covered capacity memos valid

/-- Initial invariants and numeric prefix capacity construct the actual target and full receipt. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (capacity : TargetCapacity bits values paths before memo) (memos : Memos)
    (valid : GlobalValid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Target values paths before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node result := by
  exact SourceCurrentAllocatedFiniteOrdinaryTarget.finite formulas solver inventory values paths before memo ready admitted
    available domain physicalStored mergeStored nativeStored covered
    (target_ranges formulas solver inventory bits values paths before memo ready admitted available domain physicalStored
      mergeStored nativeStored covered capacity memos valid) memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetCapacity
