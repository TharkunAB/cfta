import MicroCFTA.SourceCurrentScanNumeric
import MicroCFTA.SourceCurrentAllocatedScanCaller

/-!
# Initial numeric Scans in the complete current caller

The initial heap supplies its finite guard list. The Scan constructs its
own ranges, strict source reads, and complete returned caller context.
The returned query Frame and caller Post use the same actual inventory.
-/
namespace MicroCFTA.SourceCurrentScanCallerNumeric
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial support and reservations construct the complete Scan and its same-inventory caller Post. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (reserved : SourceCurrentScanNumericForecast.Reserved bits budget values.length classes
      (guards before.checked.native.machine.heap) profile) :
    ∃ outcome selected after saved next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver (guards before.checked.native.machine.heap)
          profile budget values classes before.checked before.fourth outcome selected after saved next,
        ScanReads receipt.actual memos final ∧
        Post formulas solver next before (advance before after saved before.merge) final ∧
        selected.Sublist classes ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values classes outcome ∧
        (advance before after saved before.merge).nodeResults = before.nodeResults ∧
        (advance before after saved before.merge).edgeResults = before.edgeResults ∧
        (advance before after saved before.merge).merge = before.merge ∧
        (advance before after saved before.merge).fourth = saved := by
  have known := SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
    frame.ready.semantic.ready.semantic.1.normal.facts
  obtain ⟨outcome, selected, after, saved, next, receipt⟩ := SourceCurrentScanNumeric.complete formulas solver
    (guards before.checked.native.machine.heap) budget values classes before.checked before.fourth inventory
    frame profile fits available initial.correct known proper reserved memos initial.globals
  obtain ⟨_other, final, reads, oldPost, _resident, selectedSublist, sound⟩ :=
    SourceCurrentAllocatedScanCaller.actual formulas solver receipt.actual initial available proper active receipt.ranges
  have post : Post formulas solver next before (advance before after saved before.merge) final :=
    ⟨⟨receipt.frame.ready, receipt.frame.admitted, oldPost.context.sound,
      oldPost.context.stored, oldPost.context.covered, oldPost.context.correct,
      oldPost.context.globals, oldPost.context.probes⟩,
      oldPost.effects, oldPost.retained, oldPost.fourthRetained⟩
  exact ⟨outcome, selected, after, saved, next, final, receipt, reads, post, selectedSublist, sound, rfl, rfl, rfl, rfl⟩

end MicroCFTA.SourceCurrentScanCallerNumeric
