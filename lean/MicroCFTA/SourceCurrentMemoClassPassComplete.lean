import MicroCFTA.SourceCurrentMemoClassPassLanguage
import MicroCFTA.SourceCurrentMemoClassPassMemos

/-!
# One finite memo-aware class pass with language and global receipts

The same returned pass supplies physical effects, merge producer histories,
independent language bounds, and ordered reads of the three global tables.
Only the merge table starts empty. The physical heap and global tables can
already contain valid entries. General Scan and runtime transfer stay separate.
-/
namespace MicroCFTA.SourceCurrentMemoClassPassComplete
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceCurrentMemoClassPass SourceCurrentMemoClassPassMemos
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- One finite cold merge-table pass derives all language, physical, and global memo conclusions. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Native width Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before SourceCurrentMemoMergeGraph.empty)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ results after saved final, ∃ actual : Pass emptyGuard conjoin clear top records values before SourceCurrentMemoMergeGraph.empty results after saved,
      PassReads actual memos final ∧ SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final ∧
      IdleReady emptyGuard conjoin after ∧ CostHeap after.machine.heap ∧ Stored after.machine.heap saved ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ path, ForestClosed path values → ForestClosed path results) ∧ CacheCovers holds ambient saved ∧ Produced clear top saved ∧
      ∀ symbol terms,
        (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
        ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
          (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms)) := by
  obtain ⟨results, after, saved, actual, finalReady, finalCosts, finalStored, kept, resultAvailable, resultDomains, origins⟩ :=
    SourceCurrentMemoClassPass.finite_cold emptyGuard conjoin clear top ranges coherent active ready costs available domains
  have stored := SourceCurrentMemoMergeEffects.stored_empty before.machine.heap
  have initialCovered : CacheCovers holds ambient SourceCurrentMemoMergeGraph.empty := by
    intro key entry found
    cases found
  obtain ⟨covered, language⟩ := SourceCurrentMemoClassPassLanguage.pass_language emptyGuard conjoin clear top holds ambient
    clearTrue topTrue conjoined actual coherent active ready costs stored available domains initialCovered
  obtain ⟨final, reads, effect⟩ := pass_memos actual coherent active ready costs stored available domains memos valid
  exact ⟨results, after, saved, final, actual, reads, effect, finalReady, finalCosts, finalStored, kept,
    resultAvailable, resultDomains, covered, origins, language⟩

end MicroCFTA.SourceCurrentMemoClassPassComplete
