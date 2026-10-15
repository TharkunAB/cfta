import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.SourceCurrentMemoMergeLanguage
import MicroCFTA.SourceCurrentMemoMergeQueryMemos

/-!
# Finite completed merge calls with independent language and actual receipts

The same finite call supplies physical effects, retained cache answers,
independent language coverage, and ordered global memo reads. An empty
result table derives all entry obligations and actual producer histories.
The initial physical heap can be warm. Lazy publication and runtime forcing
remain separate from this completed sequential graph.
-/
namespace MicroCFTA.SourceCurrentMemoMergeComplete
open Cache Language InternedConstructorTemplates InternedGuardedLanguage InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial physical and semantic cache validity derive a finite actual call and its language coverage. -/
theorem finite
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (stored : Stored before memo) (covered : CacheCovers holds ambient memo)
    (available : Available before input) :
    ∃ output after saved, Call clear top input before memo output after saved ∧
      Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧ Extends memo saved ∧
      Available after output ∧ (input.free = [] → output.free = []) ∧ Covers holds ambient input output := by
  obtain ⟨output, after, saved, actual, _⟩ :=
    SourceCurrentMemoMergeCompletion.call_complete clear top input before memo semantic costs stored available
  obtain ⟨effect, retained, finalCovered, physical, inclusion⟩ :=
    SourceCurrentMemoMergeLanguage.call_language clear top holds ambient clearTrue topTrue
      actual semantic costs stored covered available
  exact ⟨output, after, saved, actual, effect, retained, finalCovered, actual.extends,
    physical.1, physical.2, inclusion⟩

/-- An empty result table derives finite coverage and a stored producer for the exact original input. -/
theorem cold
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    ∃ output after saved, Call clear top input before empty output after saved ∧
      Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧ Produced clear top saved ∧
      Available after output ∧ (input.free = [] → output.free = []) ∧ Covers holds ambient input output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧
        Origin clear top input output := by
  obtain ⟨output, after, saved, actual, effect, retained, covered, _, result, closed, inclusion⟩ :=
    finite clear top holds ambient clearTrue topTrue input before empty semantic costs
      (stored_empty before) (SourceCurrentMemoMergeLanguage.cache_covers_empty holds ambient) available
  obtain ⟨produced, entry, found, returned, _, origin⟩ := SourceCurrentMemoMergeOrigins.cold_produced actual
  obtain ⟨same, _, _⟩ := hit_original effect.semantic (effect.keeps.available input available) retained found
  exact ⟨output, after, saved, actual, effect, retained, covered, produced, result, closed, inclusion,
    entry, found, same, returned, same ▸ origin⟩

end MicroCFTA.SourceCurrentMemoMergeComplete

namespace MicroCFTA.SourceCurrentMemoMergeComplete
open Cache Language InternedConstructorTemplates InternedGuardedLanguage InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- The same finite cold-result call derives actual global receipts, language coverage, and producer history. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (memos : Memos) (valid : Valid before memos) :
    ∃ output after saved final, Call clear top input before empty output after saved ∧
      SourceCurrentMemoMergeQueryMemos.CallReads clear top input before empty output after saved memos final ∧
      SourceCurrentSubsumesQueryMemos.Effect before after memos final ∧
      Stored after saved ∧ CacheCovers holds ambient saved ∧ Produced clear top saved ∧
      Available after output ∧ (input.free = [] → output.free = []) ∧ Covers holds ambient input output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧
        Origin clear top input output := by
  obtain ⟨output, after, saved, actual, _, stored, covered, produced, result, closed, inclusion, entry⟩ :=
    cold clear top holds ambient clearTrue topTrue input before semantic costs available
  obtain ⟨final, receipt, effect, _⟩ :=
    SourceCurrentMemoMergeQueryMemos.cold_memos actual semantic costs available memos valid
  exact ⟨output, after, saved, final, actual, receipt, effect, stored, covered, produced,
    result, closed, inclusion, entry⟩

end MicroCFTA.SourceCurrentMemoMergeComplete
