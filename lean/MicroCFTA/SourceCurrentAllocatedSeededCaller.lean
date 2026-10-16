import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedSeededReadValidity
import MicroCFTA.SourceCurrentAllocatedProbeQuery

/-!
# Full caller receipts for current first-seeded queries

The selected path support constructs checked execution and its next inventory.
The same returned state retains both outer result families, the merge table,
and the fourth memo. Global reads remain logical receipts. They do not
establish concrete host global-table execution or lazy publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededCaller
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedSeededQuery (Seeded SeededRanges)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "SeededReads" => SourceCurrentAllocatedSeededMemos.SeededReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Supplied source reads derive the full caller at their exact checked return. -/
theorem verified (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {inventory : Inventory} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {actual : Seeded values paths before.checked result after} {memos final : Memos}
    (reads : SeededReads actual memos final) (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked) :
    ∃ next, Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨next, receipt, included⟩ := SourceCurrentAllocatedSeededLanguage.Seeded.receipt
    formulas solver inventory unconstrained anchor anchorSemantic anchorReady actual ranges initial.ready.good
    ready initial.ready.scopedCache initial.ready.idle initial.admitted available growth supported proper
  have globals := SourceCurrentAllocatedSeededReadValidity.seeded unconstrained anchor anchorSemantic anchorReady
    reads ranges initial.ready.good ready initial.ready.scopedCache initial.ready.idle
    available growth supported initial.globals
  have probes := SourceCurrentAllocatedProbeQuery.seeded_heap formulas solver inventory unconstrained anchor
    anchorSemantic anchorReady actual ranges initial.ready initial.admitted available growth supported proper initial.probes
  refine ⟨next, ⟨⟨⟨receipt.good, receipt.effects.ready.semantic, receipt.effects.ready.costs,
    receipt.scopes, receipt.idle⟩, receipt.admitted,
    initial.sound.advance formulas solver _ before.fourth before.merge receipt.effects,
    initial.stored.grows receipt.effects.keeps, initial.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    globals.1, probes⟩, receipt.effects, Cache.extends_refl _, fun _ _ found => found⟩,
    receipt.available, receipt.closed, included, globals.2.1, globals.2.2⟩

/-- Legitimate entry facts construct global reads for the same actual query. -/
theorem actual (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {inventory : Inventory} {before : Caller width} {after : Checked width}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    (query : Seeded values paths before.checked result after) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked) :
    ∃ next final, SeededReads query memos final ∧ Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨final, reads, _⟩ := SourceCurrentAllocatedSeededMemos.seeded_memos unconstrained anchor
    anchorSemantic anchorReady query ranges initial.ready.good ready initial.ready.scopedCache initial.ready.idle
    available growth supported memos initial.globals
  obtain ⟨next, post⟩ := verified formulas solver unconstrained anchor anchorSemantic anchorReady reads initial
    available growth supported proper ranges
  exact ⟨next, final, reads, post⟩

/-- Initial selected support constructs finite execution and all returned caller facts. -/
theorem finite (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked) :
    ∃ result after next final, ∃ query : Seeded values paths before.checked result after,
      SeededReads query memos final ∧ Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨result, after, _, query, _⟩ := SourceCurrentAllocatedSeededLanguage.seeded_complete formulas solver
    inventory unconstrained anchor anchorSemantic anchorReady values paths before.checked ranges initial.ready.good
    ready initial.ready.scopedCache initial.ready.idle initial.admitted available growth supported proper
  obtain ⟨next, final, reads, post⟩ := actual formulas solver unconstrained anchor anchorSemantic anchorReady
    query initial available growth supported proper ranges
  exact ⟨result, after, next, final, query, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedSeededCaller
