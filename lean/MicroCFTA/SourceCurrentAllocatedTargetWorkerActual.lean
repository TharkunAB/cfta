import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedProbeTargets
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Checked receipts for literal current target returns

Every supplied successful return derives its own current target graph and
checked receipt. Initial selected domains also construct a stable literal
return. The caller endpoint retains both outer result families and the
fourth memo. Global query receipts are logical read evidence; this worker
does not execute concrete host global tables. Targets preserve common
selected subterms. They do not have an exact-language contract.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetWorkerActual
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedTargetWorker
open SourceCurrentAllocatedTargetWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "TargetRanges" => SourceCurrentAllocatedTargetGraph.TargetRanges
local notation "Receipt" => SourceCurrentAllocatedTargetComplete.Receipt
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- A supplied literal target return derives its own checked receipt and physical probes. -/
theorem verified (inventory : Inventory) {p h m s n : Nat}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {memo saved : Memo} {result : Value Symbol Guard}
    (done : target p h m s n values paths before memo = .done result after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ∃ next final, Receipt formulas solver next values paths before memo result after saved memos final ∧
      ProbeHeap after.native.machine.heap := by
  have actual := SourceCurrentAllocatedTargetWorkerSound.target_sound formulas solver inventory p h m s n
    values paths before memo ready admitted available domains stored covered ranges memos valid result after saved done
  obtain ⟨next, final, reads, receipt⟩ := SourceCurrentAllocatedTargetComplete.Target.verified
    formulas solver inventory actual ready admitted available
    domains stored covered ranges memos valid
  exact ⟨next, final, receipt, SourceCurrentAllocatedProbeTargets.target_heap reads ready available stored probes⟩

/-- Initial selected support constructs stable literal execution and the same complete checked receipt. -/
theorem finite (inventory : Inventory) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ paths, Domain path values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ∃ result after saved next final,
      StableRun (fun p h m s n => target p h m s n values paths before memo) result after saved ∧
      Receipt formulas solver next values paths before memo result after saved memos final ∧
      ProbeHeap after.native.machine.heap := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedTargetComplete.target_complete formulas solver inventory values paths before memo ready
      admitted available domains stored covered ranges memos valid
  exact ⟨result, after, saved, next, final, SourceCurrentAllocatedTargetWorkerCompletion.target_complete actual,
    receipt, SourceCurrentAllocatedProbeTargets.target_heap reads ready available stored probes⟩

/-- A literal target return retains the full caller at its computed next inventory. -/
theorem caller {inventory : Inventory} {p h m s n : Nat} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {saved : Memo} {memos : Memos} (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (ranges : TargetRanges values paths before.checked before.merge)
    (done : target p h m s n values paths before.checked before.merge = .done result after saved) :
    ∃ next final, Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → (∀ path ∈ paths, path ≠ []) →
        SourceCurrentAllocatedTargetComplete.Includes formulas solver values paths result) := by
  obtain ⟨next, final, receipt, probes⟩ := verified formulas solver inventory done initial.ready initial.admitted
    available domains initial.stored initial.covered ranges memos initial.globals initial.probes
  exact ⟨next, final, ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩,
    receipt.available, receipt.closed, receipt.included⟩

/-- Legitimate caller entry constructs a stable target return with all warm caller invariants. -/
theorem caller_finite {inventory : Inventory} {before : Caller width} {memos : Memos}
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (ranges : TargetRanges values paths before.checked before.merge) :
    ∃ result after saved next final,
      StableRun (fun p h m s n => target p h m s n values paths before.checked before.merge) result after saved ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → (∀ path ∈ paths, path ≠ []) →
        SourceCurrentAllocatedTargetComplete.Includes formulas solver values paths result) := by
  obtain ⟨result, after, saved, next, final, stable, receipt, probes⟩ := finite formulas solver inventory values paths
    before.checked before.merge initial.ready initial.admitted available domains initial.stored initial.covered ranges
    memos initial.globals initial.probes
  exact ⟨result, after, saved, next, final, stable,
    ⟨⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
      receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩,
    receipt.available, receipt.closed, receipt.included⟩

end MicroCFTA.SourceCurrentAllocatedTargetWorkerActual
