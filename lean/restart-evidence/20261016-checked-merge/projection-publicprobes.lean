import MicroCFTA.SourceCurrentConjunctionTargetProjection

#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjection.verified
#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjection.complete
#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjection.of_required
#check @MicroCFTA.SourceCurrentConjunctionTargetProjection.Receipt
#check @MicroCFTA.SourceCurrentConjunctionTargetProjection.verified
#check @MicroCFTA.SourceCurrentConjunctionTargetProjection.complete
#check @MicroCFTA.SourceCurrentConjunctionTargetProjection.of_required

namespace MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentConjunctionTargetProjection
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

-- Completion retains the exact operation state and derives its same-cache field loads.
theorem current_fields
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after final, Receipt formulas solver inventory path values before result after memos final ∧
      after.operations = before.operations ∧
      SourceCurrentConjunctionEquality.Fields before.operations after.native.machine.heap ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges := by
  obtain ⟨result, after, final, receipt⟩ := complete formulas solver inventory path values before
    ready admitted available domain memos valid
  have fields := receipt.ready.good.fields
  rw [receipt.operations] at fields
  exact ⟨result, after, final, receipt, receipt.operations, fields, receipt.nodes, receipt.edges⟩

-- The current required receipt supplies the selected domain without closing the whole forest.
theorem required_selected
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before after)
    (path : Path) (member : path ∈ selected.flatten) (proper : path ≠ [])
    (memos : Memos) (valid : Valid after.native.machine.heap memos) :
    ∃ result reached final,
      Receipt formulas solver inventory (path.map Int.ofNat) values after result reached memos final ∧
      result.free = [] ∧ ∀ holds ambient symbol terms part,
        All₂ (meaning holds ambient) values terms →
        SymbolicSignedPaths.lookup (.node symbol terms) (path.map Int.ofNat) = some part →
        meaning holds ambient result part := by
  obtain ⟨result, reached, final, receipt⟩ := of_required formulas solver inventory required path member memos valid
  have signedProper : path.map Int.ofNat ≠ [] := by
    cases path with
    | nil => exact False.elim (proper rfl)
    | cons index rest => simp
  exact ⟨result, reached, final, receipt, receipt.closed, receipt.included signedProper⟩

-- Two actual projections retain warm tables and one inventory in their literal source order.
theorem sequential
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (firstPath secondPath : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (firstDomain : ForestClosed firstPath values) (secondDomain : ForestClosed secondPath values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ first middle saved second after final,
      Receipt formulas solver inventory firstPath values before first middle memos saved ∧
      Receipt formulas solver inventory secondPath values middle second after saved final ∧
      At formulas solver inventory after ∧ after.operations = before.operations ∧
      final.query = memos.query ∧ Extends memos.unfolding final.unfolding := by
  obtain ⟨first, middle, saved, firstReceipt⟩ := complete formulas solver inventory firstPath values before
    ready admitted available firstDomain memos valid
  have middleValues : Values middle.native.machine.heap values := fun value member =>
    firstReceipt.effects.keeps.available value (available value member)
  obtain ⟨second, after, final, secondReceipt⟩ := complete formulas solver inventory secondPath values middle
    firstReceipt.ready firstReceipt.admitted middleValues secondDomain saved firstReceipt.globals.valid
  exact ⟨first, middle, saved, second, after, final, firstReceipt, secondReceipt,
    secondReceipt.admitted, secondReceipt.operations.trans firstReceipt.operations,
    secondReceipt.globals.query.trans firstReceipt.globals.query,
    extends_trans firstReceipt.globals.retained secondReceipt.globals.retained⟩

-- Root projection has exact union language and finite stable execution at the same returned heap.
theorem root_union
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : MergedColdReaderClosedInputs.ClosedValues values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after final, Receipt formulas solver inventory [] values before result after memos final ∧
      ∀ holds ambient term, meaning holds ambient result term ↔ ∃ value ∈ values, meaning holds ambient value term := by
  obtain ⟨result, after, final, receipt⟩ := complete formulas solver inventory [] values before
    ready admitted available closed memos valid
  exact ⟨result, after, final, receipt, receipt.root_exact rfl⟩

end MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes

#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.current_fields
#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.required_selected
#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.sequential
#print axioms MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.root_union
#check @MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.current_fields
#check @MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.required_selected
#check @MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.sequential
#check @MicroCFTA.SourceCurrentConjunctionTargetProjectionProbes.root_union
