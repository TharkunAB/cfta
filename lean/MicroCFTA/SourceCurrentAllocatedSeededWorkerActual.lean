import MicroCFTA.SourceCurrentAllocatedSeededWorkerSound
import MicroCFTA.SourceCurrentAllocatedSeededCaller

/-!
# Full caller receipts for literal first-seeded execution

Initial selected support constructs stable literal execution and the full
returned caller. Supplied literal success derives the same graph, reads,
and physical probes at its actual return. The merge and fourth memo remain
unchanged. Global reads are logical evidence, not host table event replay.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededWorkerActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedSeededQuery (Seeded SeededRanges)
open SourceCurrentAllocatedSeededWorker (seeded)
open SourceCurrentAllocatedSeededWorkerCompletion (StableRun)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "SeededReads" => SourceCurrentAllocatedSeededMemos.SeededReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- A literal successful return derives its own graph, reads, and complete caller. -/
theorem verified (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {inventory : Inventory} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {memos : Memos} {p h n : Nat} (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked)
    (done : seeded p h n values paths before.checked = .done result after) :
    ∃ next final, ∃ query : Seeded values paths before.checked result after,
      SeededReads query memos final ∧ Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have query := SourceCurrentAllocatedSeededWorkerSound.seeded_sound unconstrained anchor anchorSemantic anchorReady
    values paths before.checked ranges initial.ready.good ready initial.ready.scopedCache initial.ready.idle
    available growth supported p h n result after done
  obtain ⟨next, final, reads, post⟩ := SourceCurrentAllocatedSeededCaller.actual formulas solver
    unconstrained anchor anchorSemantic anchorReady query initial available growth supported proper ranges
  exact ⟨next, final, query, reads, post⟩

/-- Legitimate caller entry constructs stable literal execution and its full returned invariant. -/
theorem finite (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked) :
    ∃ result after next final,
      StableRun (fun p h n => seeded p h n values paths before.checked) result after ∧
      ∃ query : Seeded values paths before.checked result after,
        SeededReads query memos final ∧ Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
        Available after.native.machine.heap result ∧ result.free = [] ∧
        (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
        Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨result, after, next, final, query, reads, post⟩ := SourceCurrentAllocatedSeededCaller.finite formulas solver
    unconstrained anchor anchorSemantic anchorReady values paths initial available growth supported proper ranges
  exact ⟨result, after, next, final, SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete query,
    query, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedSeededWorkerActual
