import MicroCFTA.SourceCurrentMemoMergeMeasured
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MeasuredMergeIntegration
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeMeasured
open SourceCurrentMemoMergeGraph (Code Memo)

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 0 true [.node [.mk 1 true []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def base : Value Nat Bool := (children root).getD 0 .empty
private def initial : Memo Nat Bool := SourceCurrentMemoMergeGraph.empty
private def middle : Memo Nat Bool := SourceCurrentMemoMergeGraph.remember initial base base
private def saved : Memo Nat Bool := SourceCurrentMemoMergeGraph.remember middle root root

private theorem constructed : built = .done root heap := by cbv
private def code : Code Nat Bool (Value Nat Bool) :=
  .bind (.request root) fun value => .bind (.select [value]) fun _ => .pure value
private theorem actual_call : SourceCurrentMemoMergeWorker.call (fun guard => guard) true 128 0 root heap initial =
    .done root heap saved := by cbv
private theorem actual_run : SourceCurrentMemoMergeWorker.execute (fun guard => guard) true 128 0 code heap initial =
    .done root heap saved := by cbv

private theorem local_ready {clear : Bool → Bool} {top : Bool} {Output : Type}
    {cost : Nat} {code : Code Nat Bool Output} {before after : State Nat Bool}
    {memo final : Memo Nat Bool} {output : Output}
    (actual : MeasuredRun clear top cost code before memo output after final) :
    ∃ bound, ∀ fuel, bound ≤ fuel → SelectionReady fuel actual := by
  induction actual using MeasuredRun.rec
      (motive_2 := fun _ input before memo output after final actual =>
        ∃ bound, ∀ fuel, bound ≤ fuel →
          @CallSelectionReady Nat Bool inferInstance inferInstance clear top fuel _ input before memo output after final actual) with
  | pure value state memo => exact ⟨0, fun _ _ => .pure value state memo⟩
  | work job state memo => exact ⟨0, fun _ _ => .work job state memo⟩
  | select oldFuel done =>
      exact ⟨oldFuel, fun fuel enough => .select oldFuel done
        (SourceCurrentMemoMergeWorkerProofs.selection_stable clear oldFuel fuel _ _ _ _ done enough)⟩
  | request actual ih =>
      obtain ⟨bound, ready⟩ := ih
      exact ⟨bound, fun fuel enough => .request (ready fuel enough)⟩
  | bind first later firstIH lastIH =>
      obtain ⟨firstBound, firstReady⟩ := firstIH
      obtain ⟨lastBound, lastReady⟩ := lastIH
      exact ⟨max firstBound lastBound, fun fuel enough => .bind
        (firstReady fuel (by omega)) (lastReady fuel (by omega))⟩
  | hit found => exact ⟨0, fun _ _ => .hit found⟩
  | miss absent actual ih =>
      obtain ⟨bound, ready⟩ := ih
      exact ⟨bound, fun fuel enough => .miss absent (ready fuel enough)⟩

private theorem call_local_ready {clear : Bool → Bool} {top : Bool} {cost : Nat}
    {input output : Value Nat Bool} {before after : State Nat Bool} {memo final : Memo Nat Bool}
    (actual : MeasuredCall clear top cost input before memo output after final) :
    ∃ bound, ∀ fuel, bound ≤ fuel → CallSelectionReady fuel actual := by
  obtain ⟨bound, ready⟩ := local_ready (MeasuredRun.request actual)
  refine ⟨bound, ?_⟩
  intro fuel enough
  cases ready fuel enough with
  | request child => exact child

/-- Own nested ordinary misses, constructor work, and selection preserve both exact fuel indices. -/
theorem nested_misses (workExtra selectionExtra : Nat) :
    ∃ cost selectionBound,
      built = .done root heap ∧
      SourceCurrentMemoMergeGraph.Run (fun guard => guard) true code heap initial root heap saved ∧
      SourceCurrentMemoMergeWorker.execute (fun guard => guard) true (cost + workExtra)
        (selectionBound + selectionExtra) code heap initial = .done root heap saved ∧
      saved base.referenceOf = some ⟨base, base⟩ ∧ saved root.referenceOf = some ⟨root, root⟩ := by
  have graph := SourceCurrentMemoMergeWorkerProofs.execute_sound actual_run
  obtain ⟨cost, measured⟩ := of_run graph
  obtain ⟨bound, ready⟩ := local_ready measured
  exact ⟨cost, bound, constructed, measured.erase,
    run_replay measured bound (ready bound (Nat.le_refl _)) _ _ (by omega) (by omega), by cbv, by cbv⟩

/-- A following call reads the actual produced winner without changing heap or memo. -/
theorem warm_hit (workExtra selectionFuel : Nat) :
    ∃ cost selectionBound,
      SourceCurrentMemoMergeWorker.call (fun guard => guard) true cost selectionBound root heap initial = .done root heap saved ∧
      SourceCurrentMemoMergeWorker.call (fun guard => guard) true (1 + workExtra) selectionFuel root heap saved =
        .done root heap saved := by
  have graph := SourceCurrentMemoMergeWorkerProofs.call_sound actual_call
  obtain ⟨cost, measured⟩ := of_call graph
  obtain ⟨bound, ready⟩ := call_local_ready measured
  have found : saved root.referenceOf = some ⟨root, root⟩ := by cbv
  have hit : MeasuredCall (fun guard => guard) true 1 root heap saved root heap saved := .hit found
  exact ⟨cost, bound, call_replay measured bound (ready bound (Nat.le_refl _)) _ _ (Nat.le_refl _) (Nat.le_refl _),
    call_replay hit 0 (.hit found) _ _ (by omega) (Nat.zero_le _)⟩

/-- A distinct candidate keeps the exact winner published by the nested actual worker call. -/
theorem current_winner :
    SourceCurrentMemoMergeWorker.call (fun guard => guard) true 128 0 root heap initial = .done root heap saved ∧
    root ≠ Value.empty ∧ SourceCurrentMemoMergeGraph.winner saved root Value.empty = ⟨root, root⟩ ∧
    SourceCurrentMemoMergeGraph.remember saved root Value.empty = saved := by
  have found : saved root.referenceOf = some ⟨root, root⟩ := by cbv
  have kept := SourceCurrentMemoMergeGraph.winner_existing saved root Value.empty ⟨root, root⟩ found
  exact ⟨actual_call, by cbv, kept.2, kept.1⟩

end MicroCFTA.MeasuredMergeIntegration

#print axioms MicroCFTA.MeasuredMergeIntegration.nested_misses
#check @MicroCFTA.MeasuredMergeIntegration.nested_misses
#print axioms MicroCFTA.MeasuredMergeIntegration.warm_hit
#check @MicroCFTA.MeasuredMergeIntegration.warm_hit
#print axioms MicroCFTA.MeasuredMergeIntegration.current_winner
#check @MicroCFTA.MeasuredMergeIntegration.current_winner
