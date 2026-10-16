import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain

/-!
# Finite allocation prefixes for the current Region recursion

Indexed descent and inherited combination derive their actual receipts.
Their exact caller returns retain the full context, structural returned
domain, and every protected active-owner bound. No child call, range plan,
or future prefix result is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialGraph (descend prefixState)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveExcept)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq (EdgeKey Symbol Guard)] {width bound : Nat} {nodeSkip edgeSkip : Option Nat}

/-- Indexed descent constructs its literal payload and retains all current caller facts. -/
theorem descent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (combined : EqValue) (index : Nat)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (stored : Stored before) (active : ActiveExcept bound nodeSkip edgeSkip before) :
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index ∧
      Post formulas solver inventory before (descend before combined index).2 memos ∧
      Stored (descend before combined index).2 ∧ ActiveExcept bound nodeSkip edgeSkip (descend before combined index).2 := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
    initial combined index inheritedReady
  exact ⟨receipt, post, stored,
    active.advance (descend before combined index).2.checked before.fourth before.merge⟩

/-- The resident inherited-first prefix constructs its own completed result and exact caller return. -/
theorem inherited_prefix
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (stored : Stored before) (active : ActiveExcept bound nodeSkip edgeSkip before) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory
        edge.entry.key.constraint inherited before.checked combined ∧
      Post formulas solver inventory before (prefixState before edge inherited) memos ∧
      Stored (prefixState before edge inherited) ∧ ActiveExcept bound nodeSkip edgeSkip (prefixState before edge inherited) := by
  obtain ⟨combined, receipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory
    edge inherited before.checked initial.ready initial.admitted resident inheritedReady
  have effects := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
    initial edge inherited combined resident inheritedReady receipt.actual
  exact ⟨combined, receipt, effects.2, stored,
    active.advance (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited)
      before.fourth before.merge⟩

end MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes
