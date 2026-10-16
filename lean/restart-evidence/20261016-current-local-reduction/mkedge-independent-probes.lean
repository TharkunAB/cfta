import MicroCFTA.SourceCurrentAllocatedMkEdge

namespace MicroCFTA.SourceCurrentAllocatedMkEdgeProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
-- One resident source field derives the actual constructor and preserves both unrelated memo families.
theorem resident_constructor
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before) (edge : EdgeValue Symbol Guard)
    (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    ∃ loaded result after,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory edge.entry.key.symbol loaded edge.children before result after ∧
      EndpointMemoGateTrace.Valid after.native.machine.heap memos ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth ∧
      ∀ ambient term,
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          ∃ terms, term = .node edge.entry.key.symbol terms ∧
            All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) edge.children terms ∧
            SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint term = true := by
  obtain ⟨cached, loaded, found⟩ := ready.good.fields edge.entry.key edge resident
  obtain ⟨storedReady, readback⟩ := SourceEqualityConstraintFieldLookup.load_ready edge.entry.key.constraint
    before.operations.constraints ready.good.operations.constraints cached loaded found
  have field : SourceCurrentConjunctionEquality.FieldAvailable before.operations
      (SourceEqualityConjoinAllocation.readback loaded) := by
    rw [readback]
    exact ⟨cached, loaded, found⟩
  have available : Values before.native.machine.heap edge.children :=
    ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  obtain ⟨result, after, receipt⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory edge.entry.key.symbol
    loaded edge.children before ready admitted storedReady field available
  refine ⟨loaded, result, after, found, receipt,
    SourceQueryUnfoldMemo.valid_grows _ _ ready.semantic receipt.effects.keeps memos valid,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps fourth correct, ?_⟩
  intro ambient term
  simpa only [readback] using receipt.language storedReady ambient term

end MicroCFTA.SourceCurrentAllocatedMkEdgeProbes

#print axioms MicroCFTA.SourceCurrentAllocatedMkEdgeProbes.resident_constructor
#check @MicroCFTA.SourceCurrentAllocatedMkEdgeProbes.resident_constructor
