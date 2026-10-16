import MicroCFTA.SourceCurrentMemoTargetWorkerProofs

/-!
# Physical finite target execution from selected path domains

Selected original paths supply closed projected operands. Actual merge
completion discharges recursive calls. Actual-prefix word checks discharge
native intersections. Each constructed graph supplies the same executable
result and full returned states at all larger five-stage bounds. Unselected
original siblings can remain open. Warm cache language coverage is not a
physical progress premise.
-/
namespace MicroCFTA.SourceCurrentMemoTargetWorkerComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoTargetOperand SourceCurrentMemoDemandTarget
open SourceCurrentMemoTargetWorker SourceCurrentMemoTargetWorkerProofs
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Path-local projection and physical merge progress derive one finite executable operand. -/
theorem operand_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (path : List Int) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (available : Values before.machine.heap values)
    (domain : ForestClosed path values) :
    ∃ result after saved, ∃ _trace : Operand clear top path values before memo result after saved,
      SourceCurrentMemoTargetOperand.Effects emptyGuard conjoin before memo result after saved ∧
      StableRun (fun p h m s _ => operand clear top p h m s path values before memo) result after saved := by
  obtain ⟨projected, heap, projection, checked⟩ := SourceEqualityProjectionPathComplete.forest_complete
    path values before.machine.heap ready.semantic available domain
  have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
  obtain ⟨result, final, saved, call, _⟩ := SourceCurrentMemoMergeCompletion.call_complete clear top projected heap memo
    checked.2.1 physical.2.2.1 (stored.grows checked.1) checked.2.2.1
  have merged : SourceCurrentMemoMergeNative.Merge clear top projected (advanceHeap before heap) memo result
      (advanceHeap (advanceHeap before heap) final) saved := .done call
  have trace : Operand clear top path values before memo result _ saved := .force projection merged
  exact ⟨result, _, saved, trace, trace.effects ready costs stored available domain, operand_complete trace⟩

/-- Reached native ranges and path-local physical progress derive the finite source right fold. -/
theorem fold_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    ∃ result after saved, ∃ _trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved,
      SourceCurrentMemoDemandTarget.Effects emptyGuard conjoin before memo result after saved ∧
      StableRun (fun p h m s n => fold emptyGuard conjoin clear top p h m s n values seed paths before memo) result after saved := by
  induction paths generalizing before memo with
  | nil =>
      obtain ⟨result, after, saved, operand, _⟩ := operand_finite emptyGuard conjoin clear top seed values before memo ready costs stored available
        (domains _ List.mem_cons_self)
      have trace : Fold emptyGuard conjoin clear top values seed [] before memo result after saved := .nil operand
      exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains, fold_complete trace⟩
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, current, operand, first, _⟩ := operand_finite emptyGuard conjoin clear top path values before memo
            ready costs stored available (domains _ (by simp))
          have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
            intro own member
            rcases List.mem_cons.mp member with rfl | member
            · exact domains _ List.mem_cons_self
            · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
          obtain ⟨tail, later, saved, rest, remaining, _⟩ := ih middle current first.ready first.costs first.stored
            (restPlan value middle current operand) (fun value member => first.keeps.available value (available value member)) tailDomains
          obtain ⟨result, after, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin later remaining.ready value tail
            (remaining.keeps.available value first.available) remaining.available first.closed remaining.closed
            (stepPlan value middle current operand tail later saved rest) (fun _ _ => true) (fun _ _ _ => rfl)
          have trace : Fold emptyGuard conjoin clear top values seed (path :: paths) before memo result after saved := .cons operand rest step
          exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains, fold_complete trace⟩

/-- Initial physical invariants and reached checks construct the graph and its stable executable target. -/
theorem target_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (ranges : TargetRanges emptyGuard conjoin clear top values paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    ∃ result after saved, ∃ _trace : Target emptyGuard conjoin clear top values paths before memo result after saved,
      SourceCurrentMemoDemandTarget.Effects emptyGuard conjoin before memo result after saved ∧
      StableRun (fun p h m s n => target emptyGuard conjoin clear top p h m s n values paths before memo) result after saved := by
  have completed : ∃ result after saved, Target emptyGuard conjoin clear top values paths before memo result after saved := by
    cases paths with
    | nil => exact ⟨.empty, before, memo, .nil⟩
    | cons seed rest =>
        obtain ⟨result, after, saved, actual, _⟩ := fold_finite emptyGuard conjoin clear top values seed rest before memo
          ready costs stored ranges available domains
        exact ⟨result, after, saved, .cons actual⟩
  obtain ⟨result, after, saved, trace⟩ := completed
  exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains, target_complete trace⟩

end MicroCFTA.SourceCurrentMemoTargetWorkerComplete
