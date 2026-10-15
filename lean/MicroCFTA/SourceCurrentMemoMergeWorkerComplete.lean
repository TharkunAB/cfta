import MicroCFTA.SourceCurrentMemoMergeWorkerProofs
import MicroCFTA.SourceCurrentMemoMergeComplete

/-!
# Finite executable memo-aware merge calls

Initial physical invariants derive an actual finite recursive Call. That
same trace supplies a stable common bound for instruction and selection
fuel. The source cold endpoint also retains independent language coverage,
actual global receipts and producer history. No recursive completion or
future cache premise is supplied.
-/
namespace MicroCFTA.SourceCurrentMemoMergeWorkerComplete
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentMemoMergeWorker SourceCurrentMemoMergeWorkerProofs
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Warm physical invariants derive a finite actual call and one stable executable bound. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (stored : Stored before memo) (available : Available before input) :
    ∃ bound output after saved, Call clear top input before memo output after saved ∧
      (∀ fuel, bound ≤ fuel → call clear top fuel fuel input before memo = .done output after saved) ∧
      Effect before after ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) := by
  obtain ⟨output, after, saved, actual, effects⟩ := SourceCurrentMemoMergeCompletion.call_complete
    clear top input before memo semantic costs stored available
  obtain ⟨bound, stable⟩ := call_uniform actual
  exact ⟨bound, output, after, saved, actual, stable, effects⟩

/-- Empty result tables derive their physical entry invariant before executable completion. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    ∃ bound output after saved, Call clear top input before empty output after saved ∧
      (∀ fuel, bound ≤ fuel → call clear top fuel fuel input before empty = .done output after saved) ∧
      Effect before after ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) :=
  finite clear top input before empty semantic costs (stored_empty before) available

end MicroCFTA.SourceCurrentMemoMergeWorkerComplete

namespace MicroCFTA.SourceCurrentMemoMergeWorkerComplete
open Cache Language InternedConstructorTemplates InternedGuardedLanguage InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
open SourceCurrentMemoMergeWorker SourceCurrentMemoMergeWorkerProofs
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- The same executable source call retains language, actual global reads and entry provenance. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (memos : Memos) (valid : Valid before memos) :
    ∃ bound output after saved final, Call clear top input before empty output after saved ∧
      (∀ fuel, bound ≤ fuel → call clear top fuel fuel input before empty = .done output after saved) ∧
      SourceCurrentMemoMergeQueryMemos.CallReads clear top input before empty output after saved memos final ∧
      SourceCurrentSubsumesQueryMemos.Effect before after memos final ∧
      Stored after saved ∧ CacheCovers holds ambient saved ∧ Produced clear top saved ∧
      Available after output ∧ (input.free = [] → output.free = []) ∧ Covers holds ambient input output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧
        Origin clear top input output := by
  obtain ⟨output, after, saved, final, actual, reads, effects, stored, covered, produced, result, closed, inclusion, entry⟩ :=
    SourceCurrentMemoMergeComplete.source_cold holds ambient clearTrue topTrue input before semantic costs available memos valid
  obtain ⟨bound, stable⟩ := call_uniform actual
  exact ⟨bound, output, after, saved, final, actual, stable, reads, effects, stored, covered, produced, result, closed, inclusion, entry⟩

end MicroCFTA.SourceCurrentMemoMergeWorkerComplete
