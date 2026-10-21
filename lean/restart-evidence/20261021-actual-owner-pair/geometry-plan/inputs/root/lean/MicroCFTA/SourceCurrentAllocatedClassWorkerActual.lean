import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability
import MicroCFTA.SourceCurrentAllocatedProbeClassPass
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Actual checked class-pass execution and caller invariants

Initial support constructs a finite class graph and stable literal execution.
Successful execution uniqueness identifies every supplied return with that
same checked graph and reads. The result retains the computed inventory,
full caller state, probes, narrowing, and class-satisfying terms. Logical
global read receipts do not establish concrete host table execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassWorkerActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedClassWorker
open SourceCurrentAllocatedClassWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Ranges" => SourceCurrentAllocatedClassPass.Ranges
local notation "Pass" => SourceCurrentAllocatedClassPass.Pass
local notation "PassReads" => SourceCurrentAllocatedClassPass.PassReads
local notation "Receipt" => SourceCurrentAllocatedClassPass.Receipt
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Initial support constructs stable execution and the full receipt at the same checked return. -/
theorem finite (inventory : Inventory) {records : List Record} {values : List (Value Symbol Guard)}
    {before : Checked width} {memo : Memo} (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ results after saved next final,
      StableRun (fun e p h m s n => pass e p h m s n records values before memo) results after saved ∧
      ∃ actual : Pass records values before memo results after saved,
        PassReads formulas solver actual memos final ∧
        Receipt formulas solver next records values before memo results after saved memos final ∧
        ProbeHeap after.native.machine.heap := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, probes⟩ :=
    SourceCurrentAllocatedProbeClassPass.pass_complete formulas solver inventory ranges coherent active ready admitted
      available domains stored covered memos valid probes
  exact ⟨results, after, saved, next, final, SourceCurrentAllocatedClassWorkerCompletion.pass_complete actual,
    actual, reads, receipt, probes⟩

/-- A supplied successful pass has its own exact graph, reads, computed inventory, and probes. -/
theorem verified (inventory : Inventory) {e p h m s n : Nat}
    {records : List Record} {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    (done : pass e p h m s n records values before memo = .done results after saved)
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      ProbeHeap after.native.machine.heap := by
  obtain ⟨result, reached, current, next, final, stable, actual, reads, receipt, probes⟩ :=
    finite formulas solver inventory ranges coherent active ready admitted available domains stored covered memos valid probes
  obtain ⟨E, P, H, M, S, N, stable⟩ := stable
  obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedClassWorkerStability.pass_done_unique done
    (stable E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨next, final, actual, reads, receipt, probes⟩

/-- A literal pass retains all caller families and its independent forest-language bounds. -/
theorem caller {inventory : Inventory} {e p h m s n : Nat} {before : Caller width} {after : Checked width}
    {records : List Record} {values results : List (Value Symbol Guard)} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (ranges : Ranges records values before.checked before.merge)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values)
    (done : pass e p h m s n records values before.checked before.merge = .done results after saved) :
    ∃ next final, Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      Values after.native.machine.heap results ∧ ∀ ambient symbol terms,
        (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
        ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
          (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
  obtain ⟨next, final, _, _, receipt, probes⟩ := verified formulas solver inventory done ranges coherent active initial.ready
    initial.admitted available domains initial.stored initial.covered memos initial.globals initial.probes
  exact ⟨next, final, ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩,
    receipt.available, receipt.language⟩

/-- Legitimate caller entry constructs stable literal pass execution and the full returned caller. -/
theorem caller_finite {inventory : Inventory} {before : Caller width} {memos : Memos}
    {records : List Record} {values : List (Value Symbol Guard)}
    (initial : Context formulas solver inventory before memos)
    (ranges : Ranges records values before.checked before.merge)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values) :
    ∃ results after saved next final,
      StableRun (fun e p h m s n => pass e p h m s n records values before.checked before.merge) results after saved ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      Values after.native.machine.heap results ∧ ∀ ambient symbol terms,
        (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
          All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
        ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
          (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
  obtain ⟨results, after, saved, next, final, stable, _, _, receipt, probes⟩ := finite formulas solver inventory ranges
    coherent active initial.ready initial.admitted available domains initial.stored initial.covered memos initial.globals initial.probes
  exact ⟨results, after, saved, next, final, stable,
    ⟨⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
      receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩,
    receipt.available, receipt.language⟩

end MicroCFTA.SourceCurrentAllocatedClassWorkerActual
