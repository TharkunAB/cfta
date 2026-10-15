import MicroCFTA.SourceCurrentMemoMergePublishedProjection
import MicroCFTA.SourceCurrentMemoMergePublishedLift
import MicroCFTA.SourceCurrentMemoMergeNative

/-!
# Finite serial publication with independent language and native effects

Finite completed calls derive early publication and safe recursive forcing.
Conversely, published calls retain the exact completed graph and effects.
The same native call supplies its publication history and global receipts.
Concurrent forcing, literal GHC evaluation, and HashMap iteration order
remain separate representation and runtime obligations.
-/
namespace MicroCFTA.SourceCurrentMemoMergePublishedComplete
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored Effect)
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
open SourceCurrentMergeResultMemo (Producer Published)
open SourceCurrentMemoMergePublishedState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every valid published call derives independent coverage from its exact completed projection. -/
theorem verified
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    {active : List Producer} {input output : Value Symbol Guard} {before after : Heap}
    {table final : Published} {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentMemoMergePublishedGraph.Call clear top active input before table memo output after final saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (known : Known before table) (published : CompletedPublished table memo)
    (covered : CacheCovers holds ambient memo) (available : Available before input) :
    SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved ∧
      Effect before after ∧ Stored after saved ∧ Known after final ∧ CompletedPublished final saved ∧
      CacheCovers holds ambient saved ∧ Available after output ∧ (input.free = [] → output.free = []) ∧
      Covers holds ambient input output := by
  obtain ⟨lower, _, _, finalKnown, finalPublished, _⟩ :=
    SourceCurrentMemoMergePublishedProjection.call_project actual semantic costs stored known published available
  obtain ⟨effect, finalStored, finalCovered, physical, inclusion⟩ :=
    SourceCurrentMemoMergeLanguage.call_language clear top holds ambient clearTrue topTrue
      lower semantic costs stored covered available
  exact ⟨lower, effect, finalStored, finalKnown, finalPublished, finalCovered, physical.1, physical.2, inclusion⟩

/-- Legitimate warm tables derive finite publication before forcing without an ancestor-exclusion premise. -/
theorem finite
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Heap) (table : Published) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (known : Known before table) (published : CompletedPublished table memo)
    (covered : CacheCovers holds ambient memo) (available : Available before input) :
    ∃ output after saved final,
      SourceCurrentMemoMergePublishedGraph.Call clear top [] input before table memo output after final saved ∧
      SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved ∧
      Effect before after ∧ Stored after saved ∧ Known after final ∧ CompletedPublished final saved ∧
      CacheCovers holds ambient saved ∧ Extends memo saved ∧ Available after output ∧
      (input.free = [] → output.free = []) ∧ Covers holds ambient input output := by
  obtain ⟨output, after, saved, actual, effect, finalStored, finalCovered, retained, result, closed, inclusion⟩ :=
    SourceCurrentMemoMergeComplete.finite clear top holds ambient clearTrue topTrue input before memo
      semantic costs stored covered available
  obtain ⟨final, lifted, finalKnown, finalPublished⟩ :=
    SourceCurrentMemoMergePublishedLift.call_lift actual semantic costs stored available [] table known published
      (by simp [SourceCurrentMemoMergePublishedLift.Above])
  exact ⟨output, after, saved, final, lifted, actual, effect, finalStored, finalKnown, finalPublished,
    finalCovered, retained, result, closed, inclusion⟩

local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid

/-- One finite native call supplies early publication, completed producers, language coverage, and actual global reads. -/
theorem native_cold
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Available before.machine.heap input) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ output after saved final table,
      SourceCurrentMemoMergeNative.Merge clear top input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentMemoMergePublishedGraph.Call clear top [] input before.machine.heap (fun _ => none)
        SourceCurrentMemoMergeGraph.empty output after.machine.heap table saved ∧
      SourceCurrentMemoMergeNative.Reads clear top input before SourceCurrentMemoMergeGraph.empty output after saved memos final ∧
      SourceCurrentMemoMergeNative.Effects emptyGuard conjoin input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final ∧
      Known after.machine.heap table ∧ CompletedPublished table saved ∧ CacheCovers holds ambient saved ∧
      Produced clear top saved ∧ Covers holds ambient input output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧ Origin clear top input output := by
  obtain ⟨output, after, saved, final, trace, reads, effect, covered, produced, inclusion, global, entry⟩ :=
    SourceCurrentMemoMergeNative.source_cold emptyGuard conjoin holds ambient clearTrue topTrue
      input before ready costs available memos valid
  obtain ⟨heap, same, actual⟩ := trace.actual
  subst after
  obtain ⟨table, published, known, complete⟩ :=
    SourceCurrentMemoMergePublishedLift.cold_lift actual ready.semantic costs available
  exact ⟨output, advanceHeap before heap, saved, final, table, trace, published, reads, effect,
    global, known, complete, covered, produced, inclusion, entry⟩

end MicroCFTA.SourceCurrentMemoMergePublishedComplete
