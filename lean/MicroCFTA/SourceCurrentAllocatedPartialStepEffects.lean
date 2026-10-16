import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.SourceCurrentAllocatedPartialDescent

/-!
# Actual constructor and inherited-allocation caller effects

Each helper derives the context at its literal returned caller state.
Rebuilds retain the existing equality operations. Prefix and descent retain
all native and caller result tables. No result law is needed for allocation.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialStepEffects
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialState (advance)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
private theorem advance_post
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (context : Context formulas solver inventory before memos) (checked : Checked width)
    (ready : Ready checked) (admitted : At formulas solver inventory checked)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical checked))
    (probes : ProbeHeap checked.native.machine.heap) :
    Post formulas solver inventory before (advance before checked before.fourth before.merge) memos := by
  refine ⟨⟨ready, admitted, context.sound.advance formulas solver checked before.fourth before.merge effects,
    context.stored.grows effects.keeps, context.covered, ?_, ?_, probes⟩, effects,
    Cache.extends_refl _, fun _ _ found => found⟩
  · exact SourceCurrentEmptinessMemo.grows formulas solver effects.keeps before.fourth context.correct
  · exact SourceQueryUnfoldMemo.valid_grows _ _ context.ready.semantic effects.keeps memos context.globals

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Literal equal-arity raw edge construction preserves probes from its actual work inputs. -/
theorem raw_edge
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (resident : EdgeResident before.checked.native.machine.heap original)
    (available : Values before.checked.native.machine.heap children) (same : children.length = original.children.length) :
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original children before.checked
      (SourceCurrentAllocatedRawRebuild.edge original children before.checked).1
      (SourceCurrentAllocatedRawRebuild.edge original children before.checked).2 ∧
    Post formulas solver inventory before
      (advance before (SourceCurrentAllocatedRawRebuild.edge original children before.checked).2 before.fourth before.merge) memos := by
  have receipt := SourceCurrentAllocatedRawRebuild.edge_verified formulas solver inventory original children before.checked
    context.ready context.admitted resident available same
  have probes := SourceCurrentAllocatedMuRebuild.work_heap
    (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.checked.native.machine.heap context.probes
    (.edge _ _ _ available)
  exact ⟨receipt, advance_post context _ receipt.ready receipt.admitted receipt.effects probes⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Both ordered-identity modifyNode branches derive the current context at the actual return. -/
theorem modify
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available before.checked.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.checked.native.machine.heap newRows) :
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory (.node entry oldRows depth free) oldRows newRows before.checked
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).1
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2 ∧
    Post formulas solver inventory before
      (advance before (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2
        before.fourth before.merge) memos := by
  have receipt := SourceCurrentAllocatedRawRebuild.modify_verified formulas solver inventory entry oldRows newRows depth free before.checked
    context.ready context.admitted available resident
  have probes : ProbeHeap
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2.native.machine.heap := by
    by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
    · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
      exact context.probes
    · simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
      exact SourceCurrentAllocatedMuRebuild.work_heap (makeNode newRows) before.checked.native.machine.heap context.probes (.node _ resident)
  exact ⟨receipt, advance_post context _ receipt.ready receipt.admitted receipt.effects probes⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- The supplied inherited-first prefix receives its own derived ready payload. -/
theorem inherited_prefix
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (edge : EdgeValue Symbol Guard) (inherited payload : EqValue)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some payload)) :
    SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint inherited before.checked payload ∧
    Post formulas solver inventory before (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited) memos := by
  obtain ⟨chosen, receipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory edge inherited before.checked
    context.ready context.admitted resident inheritedReady
  have same := Option.some.inj (Except.ok.inj (receipt.actual.symm.trans actual))
  cases same
  exact ⟨receipt, advance_post context _ receipt.ready receipt.admitted receipt.effects context.probes⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- The actual indexed descent retains every warm table and its phase laws. -/
theorem descent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos) (combined : EqValue) (index : Nat)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints combined) :
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index ∧
    Post formulas solver inventory before (SourceCurrentAllocatedPartialGraph.descend before combined index).2 memos := by
  have receipt := SourceCurrentAllocatedPartialDescent.complete formulas solver inventory before combined index
    context.ready context.admitted context.sound inheritedReady
  exact ⟨receipt, advance_post context _ receipt.ready receipt.admitted receipt.effects context.probes⟩

end MicroCFTA.SourceCurrentAllocatedPartialStepEffects
