import MicroCFTA.SourceCurrentAllocatedSharedTargetForce

#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Retains.refl
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Retains.trans
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.advance_retains
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Force.verified
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.complete
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Receipt.fourth_correct
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Retains
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Force
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Reads
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.ForceRanges
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Receipt
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Retains.refl
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Retains.trans
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.advance_retains
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Force.verified
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.complete
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForce.Receipt.fourth_correct

namespace MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassTarget (operandPaths)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedSharedTargetState
open SourceCurrentAllocatedSharedTargetForce
open SourceCurrentMemoMergeEffects (stored_empty)
open SourceCurrentMemoMergeLanguage (cache_covers_empty)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "cold" => (SourceCurrentMemoMergeGraph.empty : Memo)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Actual required preparation initializes empty slots and a cold merge table without new cache laws.
theorem required_cold_force
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before after)
    (record : SourceEqualityClassOrder.Record) (retained : record.paths ∈ selected)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths)
    (ranges : SourceCurrentAllocatedTargetGraph.TargetRanges values (operandPaths record.paths path) after cold)
    (memos : Memos) (valid : Valid after.native.machine.heap memos) :
    ∃ value reached next final,
      Receipt formulas solver next record values after.native.machine.heap path (initial after cold) value reached memos final ∧
      reached.targets path = some value ∧ value.free = [] := by
  have ready := initial_ready formulas solver inventory record values after.native.machine.heap after cold
    required.ready required.admitted (SourceEqualityRequiredCache.pure_keeps _ required.ready.semantic.ready)
    (stored_empty _) (fun ambient => cache_covers_empty _ ambient)
  have domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values := by
    intro own present
    exact required.paths own (List.mem_flatten.mpr ⟨record.paths, retained, present⟩)
  obtain ⟨value, reached, next, final, _, receipt⟩ := complete formulas solver inventory record values
    after.native.machine.heap (initial after cold) ready required.resident domains coherent active path member
    (fun _ => ranges) memos valid
  exact ⟨value, reached, next, final, receipt, receipt.present, receipt.closed⟩

-- A completed force installs or reuses a target that can be hit with the identical full state and global tables.
theorem force_then_hit
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ value after next final,
      Receipt formulas solver next record values base path before value after memos final ∧
      ∃ hit : Force record values path after value after,
        Reads formulas solver hit final final ∧
        Available after.checked.native.machine.heap value ∧ value.free = [] ∧
        SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value := by
  obtain ⟨value, after, next, final, _, receipt⟩ := complete formulas solver inventory record values base before
    ready known domains coherent active path member ranges memos valid
  have slot := receipt.ready.receipts path value receipt.present
  exact ⟨value, after, next, final, receipt, .hit receipt.present, .hit receipt.present final,
    slot.available.1, slot.available.2, slot.included coherent active⟩

-- A forced target admits its next actual checked query and retains every stored slot through the new inventory.
theorem force_then_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (input : Value Symbol Guard) (inputAvailable : Available before.checked.native.machine.heap input) (inputClosed : input.free = [])
    (queryRanges : ∀ target middle, Force record values path before target middle →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) middle.checked) :
    ∃ target middle next current finalInventory result checked,
      Receipt formulas solver next record values base path before target middle memos current ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver finalInventory target input middle.checked result checked current ∧
      Ready formulas solver finalInventory record values base (advance middle checked) ∧
      Retains before (advance middle checked) ∧
      (advance middle checked).memo = middle.memo ∧
      (advance middle checked).targets path = some target := by
  obtain ⟨target, middle, next, current, forced, receipt⟩ := complete formulas solver inventory record values base before
    ready known domains coherent active path member ranges memos valid
  obtain ⟨finalInventory, result, checked, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver next target input middle.checked receipt.ready.checked receipt.ready.admitted receipt.available
    (receipt.effects.keeps.available input inputAvailable) receipt.closed inputClosed (queryRanges target middle forced)
    current receipt.globals.valid
  exact ⟨target, middle, next, current, finalInventory, result, checked, receipt, query,
    receipt.ready.advance finalInventory checked query.ready query.admitted query.effects,
    receipt.slots.trans (advance_retains middle checked), rfl, receipt.present⟩

end MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes

#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.required_cold_force
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.force_then_hit
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.force_then_query
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.required_cold_force
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.force_then_hit
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetForceProbes.force_then_query
