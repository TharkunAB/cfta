import MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness
import MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos

/-!
# Finite current Scan and required paths from actual allocated entry

Original construction and the live allocated precheck derive the initial
checked state. The finite Scan either refutes its stopped original class
or executes required paths for its actual selected records. The successful
branch derives the complete required worker and all global memo receipts.
No completed Scan or required worker is supplied. Later class edits and
the constrained outer caller remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionAllocatedRequired
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready Scan advanceHeap)
open SourceCurrentAllocatedNativeInventoryState (At)
open SourceCurrentConjunctionAllocatedClassEntry (prefixState)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "initialOperations" => SourceEqualityConstraintMemoAllocation.initial
local notation "precheck" => SourceEqualityPartialPrecheckAllocation.run
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}

/-- Actual allocation, construction, and precheck derive finite Scan and its successful required continuation. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (correct : SourceCurrentEmptinessMemo.Correct formulas solver heap memo)
    (memos : Memos) (globals : Valid heap memos) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (precheck loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
          SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches edge.children
            (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo →
          ∃ outcome selected after saved next,
            ∃ actual : Scan budget unconstrained reaches edge.children (output.map Record.paths)
              (prefixState width heap loaded inherited finalCache) memo outcome selected after saved,
            Ready after ∧ At formulas solver next after ∧
            (∀ rejected, outcome = some rejected → rejected ∈ output.map Record.paths ∧
              ∀ ambient symbol terms,
                All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                  edge.children terms → ¬ClassSat (.node symbol terms) rejected) ∧
            (outcome = none → ∃ kept scanMemos finalMemos requiredInventory results requiredHeap,
              SourceCurrentConjunctionSelectedRecords.Retained actual output kept ∧ kept.Sublist output ∧
              kept.map Record.paths = selected ∧
              (∀ record ∈ kept, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths) ∧
              SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos scanMemos ∧
              SourceCurrentConjunctionRequired.Receipt formulas solver requiredInventory selected edge.children results
                after (advanceHeap after requiredHeap) ∧
              SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
                edge.children results after.native.machine.heap requiredHeap scanMemos finalMemos ∧
              Valid requiredHeap finalMemos ∧
              SourceCurrentEmptinessMemo.Correct formulas solver requiredHeap saved) := by
  obtain ⟨loaded, found, readback, storedReady, live⟩ :=
    SourceCurrentConjunctionAllocatedClassEntry.entry width history valid expression covered value heap built edge resident
  have initialFields := SourceCurrentClassHistoryEntry.constructed width history valid expression covered value heap built
  have available := (initialFields.2.2.2.2.2.2 edge resident).1
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output done ranges
  have checked := live inherited inheritedReady output done
  have initialAdmission := SourceCurrentConjunctionAllocatedScanSoundness.prefix_admitted width heap
    checked.1.good.native.machine.1 loaded inherited finalCache formulas solver
  obtain ⟨records, own, originalClasses, order, recordFields⟩ := checked.2.2.2.2
  have active : ∀ paths ∈ output.map Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (recordFields record present).2.2
  have proper : ∀ record ∈ output, ∀ path ∈ record.paths, path ≠ [] :=
    fun record member => checked.2.2.2.1 record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
  obtain ⟨outcome, selected, after, saved, actual, _⟩ :=
    SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches edge.children
      (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo checked.1 available
      checked.2.2.2.1 correct ranges
  obtain ⟨next, finalReady, finalAdmission, _, _, _, _, sound⟩ :=
    SourceCurrentConjunctionClassScanSoundness.verified formulas solver _ actual checked.1 initialAdmission available
      checked.2.2.2.1 active correct ranges
  refine ⟨outcome, selected, after, saved, next, actual, finalReady, finalAdmission, ?_, ?_⟩
  · intro rejected stopped
    have member : rejected ∈ output.map Record.paths := by
      subst outcome
      exact SourceCurrentConjunctionClassScan.stopped_member actual
    exact ⟨member, sound rejected stopped⟩
  · intro successful
    subst outcome
    exact SourceCurrentConjunctionRequiredGlobalMemos.records_required_memos formulas solver _ output actual
      checked.1 initialAdmission available proper recordFields correct ranges memos globals

end MicroCFTA.SourceCurrentConjunctionAllocatedRequired
