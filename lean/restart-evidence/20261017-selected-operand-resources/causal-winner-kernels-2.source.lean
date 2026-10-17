import MicroCFTA.SourceCurrentMemoMergeMass
import MicroCFTA.SourceCurrentMemoMergeWorkerProofs
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace MicroCFTA.CausalMergeWinnerKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
local notation "V" => Value Nat Bool
local notation "H" => State Nat Bool
private def expression : InternedNestedConstruction.Syntax Nat Bool := .node [.mk 0 true []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : V := match built with | .done value _ => value | .pending .. => .empty
private def heap : H := built.state
private def observed := SourceCurrentMemoMergeWorker.call (fun guard => guard) true 20 1 input heap empty
private def after : H := observed.heap
private def completed : Memo Nat Bool := observed.memo
private def nestedCode : Code Nat Bool V := .bind (.request input) fun _ => .pure .empty

private theorem constructed : built = .done input heap := by cbv
private theorem actualDone : SourceCurrentMemoMergeWorker.call (fun guard => guard) true 20 1 input heap empty =
    .done input after completed := by cbv
private theorem actualCall : Call (fun guard => guard) true input heap empty input after completed :=
  SourceCurrentMemoMergeWorkerProofs.call_sound actualDone
private theorem inputAvailable : Available heap input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result input heap constructed
private theorem physical : SourceCurrentMemoMergeEffects.Stored after completed := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input heap constructed
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  exact (SourceCurrentMemoMergeEffects.cold_effects actualCall semantic costs inputAvailable).2.1
private theorem stored : InternedValueMassHeap.Stored (InternedValueMassHeap.initialBound after) after := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input heap constructed
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  have effects := SourceCurrentMemoMergeEffects.cold_effects actualCall semantic costs inputAvailable
  exact InternedValueMassHeap.initial after effects.1.semantic.ready.semantic.1.normal.facts
private theorem published : completed input.referenceOf = some ⟨input, input⟩ := by cbv

/-- An actual nested request publishes a larger winner before a distinct candidate returns. -/
theorem nested_publication :
    built = .done input heap ∧
    Run (fun guard => guard) true nestedCode heap empty .empty after completed ∧
    SourceCurrentMemoMergeOrigins.Produced (fun guard => guard) true completed ∧
    SourceCurrentMemoMergeEffects.Stored after completed ∧
    InternedValueMassHeap.Stored (InternedValueMassHeap.initialBound after) after ∧
    (winner completed input .empty).result = input ∧
    input ≠ .empty ∧ InternedValueMass.value input = 3 ∧
    InternedValueMass.value (Value.empty : V) = 1 ∧
    InternedValueMass.value (Value.empty : V) < InternedValueMass.value (winner completed input .empty).result ∧
    InternedValueMass.value (winner completed input .empty).result ≤ InternedValueMassHeap.initialBound after := by
  have winnerSame := (winner_existing completed input .empty ⟨input, input⟩ published).2
  refine ⟨constructed, .bind (.request actualCall) (.pure (Value.empty : V) after completed),
    SourceCurrentMemoMergeOrigins.call_produced actualCall (SourceCurrentMemoMergeOrigins.produced_empty _ _),
    physical, stored, congrArg Entry.result winnerSame, ?_, ?_, rfl, ?_,
    (SourceCurrentMemoMergeMass.winner_bound physical stored input .empty (empty_available after)).2⟩
  · cbv; intro impossible; cases impossible
  · cbv
  · rw [winnerSame]
    cbv

/-- The earlier returned winner bypasses the body and survives a later losing completion. -/
theorem warm_larger_winner :
    remember completed input .empty = completed ∧
    SourceCurrentMemoMergeWorker.call (fun guard => guard) true 1 0 input after
      (remember completed input .empty) =  .done input after completed ∧
    Call (fun guard => guard) true input after completed input after completed ∧
    InternedValueMass.value (winner completed input .empty).result ≤ InternedValueMassHeap.initialBound after ∧
    InternedValueMass.value (Value.empty : V) < InternedValueMass.value (winner completed input .empty).result := by
  have unchanged := (winner_existing completed input .empty ⟨input, input⟩ published).1
  have warm := SourceCurrentMemoMergeWorker.call_hit (fun guard => guard) true 0 0 input after completed
    ⟨input, input⟩ published
  exact ⟨unchanged, by simpa only [unchanged] using warm, .hit published,
    nested_publication.2.2.2.2.2.2.2.2.2.2, nested_publication.2.2.2.2.2.2.2.2.2.1⟩

end MicroCFTA.CausalMergeWinnerKernels

#print axioms MicroCFTA.CausalMergeWinnerKernels.nested_publication
#check @MicroCFTA.CausalMergeWinnerKernels.nested_publication
#print axioms MicroCFTA.CausalMergeWinnerKernels.warm_larger_winner
#check @MicroCFTA.CausalMergeWinnerKernels.warm_larger_winner
