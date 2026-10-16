import MicroCFTA.SourceCurrentAllocatedProbeGates
import MicroCFTA.SourceCurrentAllocatedProbeConjunction
import MicroCFTA.SourceCurrentAllocatedSeededLanguage
import MicroCFTA.SourceCurrentConjunctionClassScanCompletion

/-!
# Filtered probes through current refused queries and class scans

The source fold projects its head, completes its tail, and executes the
actual checked request. Its finite physical receipts supply reached input
facts. The proof derives probes separately from those receipts. Class scans
retain only their actual visited prefix, including the early stop.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeQuery
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentConjunctionClassScan (Ready advanceHeap primary_effects secondary_effects memo_effects Scan)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
open InternedFreshOrdinaryProbeHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] in
/-- Literal projection retains the same checked tables and its actual probe heap. -/
theorem operand_heap {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {result : Value Symbol Guard}
    (actual : Operand path values before result after) (ready : Ready before)
    (available : Values before.native.machine.heap values) (probes : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases actual with
  | force heap projected =>
      exact SourceCurrentAllocatedProbeExposure.forest_heap projected ready.semantic ready.costs available probes

private theorem fold_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width} {result : Value Symbol Guard}
    (actual : Fold values paths before result after) (ranges : FoldRanges values paths before)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) :
    ∃ next, SourceCurrentAllocatedSeededLanguage.Receipt formulas solver next before result after := by
  obtain ⟨chosen, reached, next, completed, receipt, _⟩ := SourceCurrentAllocatedSeededLanguage.fold_complete
    formulas solver inventory unconstrained anchor anchorSemantic anchorReady values paths before ranges
      ready.good (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
      ready.scopedCache ready.idle admitted available growth supported proper
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact ⟨next, receipt⟩

/-- Actual fold recursion derives probes without a completed child or final-probe premise. -/
theorem fold_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width} {result : Value Symbol Guard}
    (actual : Fold values paths before result after) (ranges : FoldRanges values paths before)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  induction actual generalizing inventory with
  | one operand => exact operand_heap operand ready available probes
  | @cons path before value middle next paths tail later fuel result after operand rest native ih =>
      cases ranges with
      | cons remaining _ =>
          have first := SourceCurrentAllocatedSeededOperandLanguage.Operand.effects unconstrained anchor anchorSemantic anchorReady
            operand ready.good (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
            ready.scopedCache ready.idle available growth (supported path List.mem_cons_self)
          have middleReady : Ready middle := ⟨first.1, first.2.1.ready.semantic, first.2.1.ready.costs, first.2.2.2.1, first.2.2.2.2.1⟩
          have middleAdmission : At formulas solver inventory middle := by
            cases operand with
            | force heap projected => exact admitted.advance ⟨heap, before.operations⟩ first.2.2.1
          have middleValues : Values middle.native.machine.heap values :=
            fun value member => first.2.1.keeps.available value (available value member)
          have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
          have tailProper := fun path member => proper path (List.mem_cons_of_mem _ member)
          have tailRanges := remaining value middle operand
          have laterProbes := ih inventory tailRanges middleReady middleAdmission middleValues
            (grows_trans growth first.2.1.keeps.growth) tailSupport tailProper (operand_heap operand ready available probes)
          obtain ⟨_, receipt⟩ := fold_receipt formulas solver inventory unconstrained anchor anchorSemantic anchorReady rest
            tailRanges middleReady middleAdmission middleValues (grows_trans growth first.2.1.keeps.growth) tailSupport tailProper
          exact SourceCurrentAllocatedMuRebuild.trace_heap native receipt.effects.ready.semantic laterProbes

/-- The actual first-seed rotation retains probes at every checked prefix. -/
theorem seeded_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width} {result : Value Symbol Guard}
    (actual : Seeded values paths before result after) (ranges : SeededRanges values paths before)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | nil => exact probes
  | nonempty fold =>
      apply fold_heap formulas solver inventory unconstrained anchor anchorSemantic anchorReady fold ranges ready admitted available growth
      · intro path member
        rcases List.mem_append.mp member with tail | seed
        · exact supported path (List.mem_cons_of_mem _ tail)
        · exact supported path (by cases List.mem_singleton.mp seed; exact List.mem_cons_self)
      · intro path member
        rcases List.mem_append.mp member with tail | seed
        · exact proper path (List.mem_cons_of_mem _ tail)
        · exact proper path (by cases List.mem_singleton.mp seed; exact List.mem_cons_self)
      · exact probes

/-- A current false class supplies anchored support and its actual final probe heap. -/
theorem false_class_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
    {paths : Class} {values : List (Value Symbol Guard)} {before after : Checked width} {anchor : State Symbol Guard}
    {query : Value Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (actual : Seeded values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query after)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor))
    (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  have first := secondary_effects unconstrained gate ready available
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, support⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have anchorProbes := (SourceCurrentAllocatedProbeGates.Secondary.class_effects unconstrained gate ready.semantic ready.costs available probes).2.2.2
  apply seeded_heap formulas solver inventory unconstrained anchor anchorSemantic anchorReady actual ranges first.1
    (admitted.advance ⟨anchor, before.operations⟩ (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1))
    anchorValues (grows_refl anchor)
  · intro path member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact support original included
  · intro path member empty
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact proper original included (List.map_eq_nil_iff.mp empty)
  · exact anchorProbes

end MicroCFTA.SourceCurrentAllocatedProbeQuery
