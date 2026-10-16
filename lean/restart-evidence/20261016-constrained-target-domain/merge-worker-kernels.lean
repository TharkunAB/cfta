import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeWorker

namespace MicroCFTA.FiniteOrdinaryMergeWorkerReview
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "Ready" => SourceCurrentConjunctionRowsAllocation.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "StructuralStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "call" => SourceCurrentAllocatedMergeWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The first actual result supplies every initial physical/domain fact for the second call.
theorem serial_supplied_calls (clear : Guard → Bool) (w₁ s₁ w₂ s₂ : Nat)
    (input first second : Value Symbol Guard) (before middle after : Physical) (memo current saved : Memo)
    (ready : Ready before) (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input)
    (one : call clear w₁ s₁ input before memo = .done first middle current)
    (two : call clear w₂ s₂ first middle current = .done second after saved) :
    SourceCurrentAllocatedMergeGraph.Call clear input before memo first middle current ∧
      SourceCurrentAllocatedMergeGraph.Call clear first middle current second after saved ∧
      Effects before after ∧ PhysicalStored after.heap saved ∧ StructuralStored saved ∧
      Available after.heap first ∧ DNode first ∧ Available after.heap second ∧ DNode second := by
  obtain ⟨graphOne, effectsOne, physicalOne, structuralOne, availableOne, domainOne⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeWorker.verified one ready physical structural available domain
  obtain ⟨graphTwo, effectsTwo, physicalTwo, structuralTwo, availableTwo, domainTwo⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeWorker.verified two effectsOne.ready physicalOne structuralOne availableOne domainOne
  exact ⟨graphOne, graphTwo, effectsOne.trans effectsTwo, physicalTwo, structuralTwo,
    effectsTwo.keeps.available first availableOne, domainOne, availableTwo, domainTwo⟩

-- Finite literal completion composes twice at the actual generated operand and warm returned memo.
theorem finite_then_generated (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : Ready before) (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input) :
    ∃ w₁ s₁ first middle current w₂ s₂ second after saved,
      call clear w₁ s₁ input before memo = .done first middle current ∧
      call clear w₂ s₂ first middle current = .done second after saved ∧
      (∀ w s, w₁ ≤ w → s₁ ≤ s → call clear w s input before memo = .done first middle current) ∧
      (∀ w s, w₂ ≤ w → s₂ ≤ s → call clear w s first middle current = .done second after saved) ∧
      Effects before after ∧ PhysicalStored after.heap saved ∧ StructuralStored saved ∧
      Available after.heap first ∧ DNode first ∧ Available after.heap second ∧ DNode second := by
  obtain ⟨w₁, s₁, first, middle, current, one, stableOne, effectsOne, physicalOne, structuralOne, availableOne, domainOne⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeWorker.finite clear input before memo ready physical structural available domain
  obtain ⟨w₂, s₂, second, after, saved, two, stableTwo, effectsTwo, physicalTwo, structuralTwo, availableTwo, domainTwo⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeWorker.finite clear first middle current effectsOne.ready physicalOne structuralOne availableOne domainOne
  exact ⟨w₁, s₁, first, middle, current, w₂, s₂, second, after, saved, one, two, stableOne, stableTwo,
    effectsOne.trans effectsTwo, physicalTwo, structuralTwo, effectsTwo.keeps.available first availableOne,
    domainOne, availableTwo, domainTwo⟩
end MicroCFTA.FiniteOrdinaryMergeWorkerReview
#print axioms MicroCFTA.FiniteOrdinaryMergeWorkerReview.serial_supplied_calls
#check @MicroCFTA.FiniteOrdinaryMergeWorkerReview.serial_supplied_calls
#print axioms MicroCFTA.FiniteOrdinaryMergeWorkerReview.finite_then_generated
#check @MicroCFTA.FiniteOrdinaryMergeWorkerReview.finite_then_generated
