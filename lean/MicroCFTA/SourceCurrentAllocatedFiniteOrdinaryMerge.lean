import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache
import MicroCFTA.SourceCurrentAllocatedMerge

/-!
# Actual memo-aware merge domain preservation

Mutual induction follows the current completed Run and Call graph. Each
recursive request derives its domain result from its own body or captured
winner. The allocated graph has an exact heap/result/memo erasure to that
same completed graph. No uncached worker or historical execution supplies
the result. Finite completion uses the current allocated call constructor.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMerge
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect effect_refl)
open SourceCurrentAllocatedFiniteOrdinaryMergeCode (Certified ValuePost body_certified)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "StructuralStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

section Generic

/-- Actual recursive instructions derive domain results and retain all physical and structural cache facts. -/
theorem run_domain {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      PhysicalStored before memo → StructuralStored memo → Certified clear code before post →
      Effect before after ∧ PhysicalStored after saved ∧ StructuralStored saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → PhysicalStored before memo → StructuralStored memo →
          ValuePost before input → Effect before after ∧ PhysicalStored after saved ∧ StructuralStored saved ∧ ValuePost after output) with
  | pure value state memo =>
      intro post semantic costs physical structural checked
      exact ⟨effect_refl _ semantic costs, physical, structural, checked⟩
  | work job state memo =>
      intro post semantic costs physical structural checked
      exact ⟨checked.1, physical.grows checked.1.keeps, structural, checked.2⟩
  | select fuel done =>
      intro post semantic costs physical structural checked
      have actualEffect := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨actualEffect.keeps, actualEffect.semantic, actualEffect.costs⟩
      exact ⟨effect, physical.grows effect.keeps, structural, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical structural checked
      obtain ⟨effect, physicalAfter, structuralAfter, returned⟩ := ih semantic costs physical structural checked.1
      exact ⟨effect, physicalAfter, structuralAfter, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical structural checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstStructural, valid⟩ := ihFirst intermediate semantic costs physical structural firstChecked
      obtain ⟨laterEffect, laterPhysical, laterStructural, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstPhysical firstStructural (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterStructural, returned⟩
  | hit found =>
      rename_i semantic costs physical structural inputPost
      have result := SourceCurrentMemoMergeEffects.hit_original semantic inputPost.1 physical found
      have domain := SourceCurrentAllocatedFiniteOrdinaryMergeCache.hit_domain semantic inputPost.1 physical structural inputPost.2 found
      exact ⟨effect_refl _ semantic costs, physical, structural, result.2.1, domain.2⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical structural inputPost
      obtain ⟨effect, physicalAfter, structuralAfter, candidatePost⟩ :=
        ih _ semantic costs physical structural (body_certified _ _ input before semantic costs inputPost.1 inputPost.2)
      have inputAvailable := effect.keeps.available input inputPost.1
      have closed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed after
        effect.semantic.ready.semantic.1.normal.facts.coherent candidate candidatePost.1 candidatePost.2
      have completed := SourceCurrentMemoMergeEffects.stored_remember physicalAfter input candidate inputAvailable candidatePost.1 (fun _ => closed)
      have structuralCompleted := SourceCurrentAllocatedFiniteOrdinaryMergeCache.remember_stored structuralAfter input candidate (fun _ => candidatePost.2)
      have winner := SourceCurrentMemoMergeEffects.hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      have winnerDomain := SourceCurrentAllocatedFiniteOrdinaryMergeCache.hit_domain effect.semantic inputAvailable completed
        structuralCompleted inputPost.2 (winner_found current input candidate)
      exact ⟨effect, completed, structuralCompleted, winner.2.1, winnerDomain.2⟩

/-- Actual hits and recursive misses derive finite ordinary output from the captured input. -/
theorem call_domain {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (physical : PhysicalStored before memo) (structural : StructuralStored memo)
    (available : Available before input) (domain : DNode input) :
    Effect before after ∧ PhysicalStored after saved ∧ StructuralStored saved ∧ ValuePost after output :=
  run_domain (.request actual) ValuePost semantic costs physical structural
    ⟨⟨available, domain⟩, fun _ _ _ returned => returned⟩

end Generic

section Allocated
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Exact allocated erasure preserves the actual heap, output, memo, and derived domain. -/
theorem allocated {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : Physical} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input) :
    SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      StructuralStored saved ∧ Available after.heap output ∧ DNode output := by
  have effects := actual.verified ready physical available
  have result := call_domain actual.graph ready.semantic ready.costs physical structural available domain
  exact ⟨effects.1, effects.2.1, result.2.2.1, effects.2.2.1, result.2.2.2.2⟩

/-- Initial admitted physical and structural tables construct finite allocated merge completion. -/
theorem finite (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical)
    (memo : SourceCurrentAllocatedMergeGraph.Memo) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input) :
    ∃ output after saved, SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ PhysicalStored after.heap saved ∧
      StructuralStored saved ∧ Available after.heap output ∧ DNode output := by
  obtain ⟨output, after, saved, actual, _⟩ :=
    SourceCurrentAllocatedMergePhysical.call_complete clear input before memo ready physical available
  exact ⟨output, after, saved, actual, allocated actual ready physical structural available domain⟩

/-- The actual checked merge retains native certificates and derives ordinary result admission. -/
theorem merge {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : Checked width} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMerge.Merge clear input before memo output after saved)
    (ready : ClassReady before) (physical : PhysicalStored before.native.machine.heap memo)
    (structural : StructuralStored memo) (native : NativeStored before.native)
    (available : Available before.native.machine.heap input) (domain : DNode input) :
    ClassReady after ∧ PhysicalStored after.native.machine.heap saved ∧ StructuralStored saved ∧
      NativeStored after.native ∧ Available after.native.machine.heap output ∧ DNode output ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
        (SourceCurrentAllocatedNativeEffects.physical after) := by
  cases actual with
  | done call =>
      have result := allocated call ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩ physical structural available domain
      exact ⟨SourceCurrentConjunctionClassScan.advance_ready before _ ready result.1,
        result.2.1, result.2.2.1, SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ native,
        result.2.2.2.1, result.2.2.2.2, result.1⟩

end Allocated

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMerge
