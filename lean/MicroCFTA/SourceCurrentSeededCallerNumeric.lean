import MicroCFTA.SourceCurrentConstrainedCapSeededNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Initial numeric first-seeded queries in the full caller

The initial producer constructs its own actual query and logical reads.
Its same return retains the query Frame, caller Post, initial forecast,
all outer result tables, fourth memo, and Merge table. Selected paths
need no whole-forest closedness or finite input caps.
-/
namespace MicroCFTA.SourceCurrentSeededCallerNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentConstrainedCapSeededForecast (SeededReserved finalProfile fuel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable [DecidableEq (EdgeKey Symbol Guard)] {width bits : Nat}

/-- A complete checked receipt retains all caller laws at the receipt's same inventory and state. -/
theorem of_receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory next : Inventory} {before : Caller width} {after : Checked width}
    {value : Value Symbol Guard} {memos final : Memos}
    (initial : Context formulas solver inventory before memos)
    (receipt : SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next before.checked value after memos final) :
    Post formulas solver next before (advance before after before.fourth before.merge) final := by
  exact ⟨⟨receipt.frame.ready, receipt.frame.admitted,
    initial.sound.advance formulas solver _ before.fourth before.merge receipt.effects,
    initial.stored.grows receipt.effects.keeps, initial.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    receipt.globals.valid, receipt.probes initial.probes⟩,
    receipt.effects, Cache.extends_refl _, fun _ _ found => found⟩

variable [DecidableEq Symbol]

/-- Initial selected support and pure reservations construct the full caller at its computed query bounds. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Caller (bits + 2))
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (reserved : SeededReserved bits values.length paths profile) :
    ∃ result after next final,
      ∃ actual : SourceCurrentAllocatedSeededQuery.Seeded values paths before.checked result after,
      SourceCurrentAllocatedSeededMemos.SeededReads actual memos final ∧
      SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next before.checked result after memos final ∧
      Post formulas solver next before (advance before after before.fourth before.merge) final ∧
      Fits (finalProfile values.length paths profile) after ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      (advance before after before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before after before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before after before.fourth before.merge).fourth = before.fourth ∧
      (advance before after before.fourth before.merge).merge = before.merge ∧
      SourceCurrentAllocatedSeededWorker.seeded
        (fuel values.length paths profile) (fuel values.length paths profile) (fuel values.length paths profile)
        values paths before.checked = .done result after ∧
      (∀ projection reader native, fuel values.length paths profile ≤ projection →
        fuel values.length paths profile ≤ reader → fuel values.length paths profile ≤ native →
        SourceCurrentAllocatedSeededWorker.seeded projection reader native values paths before.checked = .done result after) := by
  obtain ⟨result, after, next, final, actual, reads, receipt, finalFits, included, done⟩ :=
    SourceCurrentConstrainedCapSeededNumeric.complete formulas solver inventory unconstrained anchor anchorSemantic anchorReady
      values paths before.checked profile frame fits available growth supported proper reserved memos initial.globals
  exact ⟨result, after, next, final, actual, reads, receipt, of_receipt formulas solver initial receipt,
    finalFits, included, rfl, rfl, rfl, rfl, done,
    fun _ _ _ enoughP enoughR enoughN => SourceCurrentAllocatedSeededWorkerStability.seeded_done_stable done enoughP enoughR enoughN⟩

end MicroCFTA.SourceCurrentSeededCallerNumeric
