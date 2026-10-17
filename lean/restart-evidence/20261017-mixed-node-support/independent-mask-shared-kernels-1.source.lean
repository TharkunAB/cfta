import MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
import MicroCFTA.SourceCurrentConstrainedCapEditSupport
import MicroCFTA.SourceCurrentConstrainedCapSharedSupport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.IndependentMaskSharedKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityEdits SourceCurrentEditDomains
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentHereditaryConstruction (MuStored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos

/-- The conditional actual edit relation retains the cap on that same returned value. -/
theorem actual_edit_cap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    (annotation : Guard → Prop)
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {edits : Edits EqualityNormalize.Path} {value result : Value Symbol Guard}
    {before after : SharedState width} {memos final : Memos}
    {actual : EditNode record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (leaves : SourceCurrentConstrainedCapEditSupport.NodeLeaves annotation actual)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory) (depth : Nat)
    (populated : Populated edits) (nonempty : HasLeaf edits)
    (allowed : SourceEqualitySharedEditEffects.Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (stored : MuStored annotation before.checked.native.machine.heap)
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth value)
    (placed : SourceCurrentConstrainedCapEditSupport.AtLeaves annotation edits value) :
    MuStored annotation after.checked.native.machine.heap ∧ Preserves annotation value result ∧
      SourceCurrentConstrainedCap.Cap annotation depth result := by
  have returned := SourceCurrentConstrainedCapEditSupport.node_with_leaf_certificates annotation reads leaves
    inventory depth populated nonempty allowed ready available safe valid stored bounded placed
  exact ⟨returned.1, returned.2, SourceCurrentConstrainedCapMaskCharacterization.preserves_cap returned.2 bounded⟩

end MicroCFTA.IndependentMaskSharedKernels

#print axioms MicroCFTA.IndependentMaskSharedKernels.actual_edit_cap
#check @MicroCFTA.IndependentMaskSharedKernels.actual_edit_cap
