import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedScanReadValidity
import MicroCFTA.SourceCurrentConjunctionClassScanSoundness
import MicroCFTA.SourceCurrentAllocatedProbeScan

/-!
# Full caller receipts for current class scans

Strict primary reads retain the exact queried source nodes. The actual
returned checked state receives its computed inventory and caller context.
A stopped class refutes every accepted original forest. Selected classes
retain their original order and multiplicity. Global reads remain logical
evidence rather than concrete host table events.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanCaller
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Scan)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Every stopped result names an original class that no accepted original forest satisfies. -/
def StoppedSound (values : List (Value Symbol Guard)) (classes : Constraints) (outcome : Option Class) : Prop :=
  ∀ paths, outcome = some paths → paths ∈ classes ∧ ∀ ambient symbol terms,
    All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
      ¬ClassSat (.node symbol terms) paths

/-- Supplied strict reads derive the full caller at their actual Scan return. -/
theorem verified {inventory : Inventory} {budget : Nat} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {saved : Memo} {memos final : Memos}
    {actual : Scan budget unconstrained reaches values classes before.checked before.fourth outcome selected after saved}
    (reads : ScanReads actual memos final) (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth) :
    ∃ next, Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      Values after.native.machine.heap values ∧ selected.Sublist classes ∧
      StoppedSound formulas solver values classes outcome := by
  obtain ⟨next, ready, admitted, effects, resident, correct, retained, sound⟩ :=
    SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory actual initial.ready initial.admitted
      available proper active initial.correct ranges
  have globals := SourceCurrentAllocatedScanReadValidity.scan reads initial.ready available proper
    formulas solver initial.correct ranges initial.globals
  have probes := SourceCurrentAllocatedProbeScan.scan_heap formulas solver inventory actual initial.ready initial.admitted
    available proper initial.correct ranges initial.probes
  refine ⟨next, ⟨⟨ready, admitted, initial.sound.advance formulas solver _ saved before.merge effects,
    initial.stored.grows effects.keeps, initial.covered, correct, globals.1, probes⟩,
    effects, Cache.extends_refl _, retained⟩, resident,
    SourceCurrentConjunctionClassScan.selected_sublist actual, ?_⟩
  intro paths stopped
  refine ⟨?_, sound paths stopped⟩
  subst outcome
  exact SourceCurrentConjunctionClassScan.stopped_member actual

/-- Legitimate entry constructs strict source reads for the same actual Scan. -/
theorem actual {inventory : Inventory} {budget : Nat} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {saved : Memo} {memos : Memos}
    (scan : Scan budget unconstrained reaches values classes before.checked before.fourth outcome selected after saved)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth) :
    ∃ next final, ScanReads scan memos final ∧ Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      Values after.native.machine.heap values ∧ selected.Sublist classes ∧
      StoppedSound formulas solver values classes outcome := by
  obtain ⟨final, reads, _⟩ := SourceCurrentAllocatedScanReadValidity.construct scan initial.ready available proper
    formulas solver initial.correct ranges memos initial.globals
  obtain ⟨next, post⟩ := verified formulas solver reads initial available proper active ranges
  exact ⟨next, final, reads, post⟩

/-- Initial caller facts and reached word bounds construct finite Scan and full return facts. -/
theorem finite {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth) :
    ∃ outcome selected after saved next final,
      ∃ scan : Scan budget unconstrained reaches values classes before.checked before.fourth outcome selected after saved,
        ScanReads scan memos final ∧ Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        Values after.native.machine.heap values ∧ selected.Sublist classes ∧
        StoppedSound formulas solver values classes outcome := by
  obtain ⟨outcome, selected, after, saved, scan, _⟩ := SourceCurrentConjunctionClassScanCompletion.finite
    formulas solver budget unconstrained reaches values classes before.checked before.fourth initial.ready available
    proper initial.correct ranges
  obtain ⟨next, final, reads, post⟩ := actual formulas solver scan initial available proper active ranges
  exact ⟨outcome, selected, after, saved, next, final, scan, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedScanCaller
