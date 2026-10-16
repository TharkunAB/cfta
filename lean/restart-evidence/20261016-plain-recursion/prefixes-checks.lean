import MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes.descent
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes.descent
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes.inherited_prefix
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainPrefixes.inherited_prefix

namespace PlainPrefixesChecks
open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance
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

theorem resident_prefix_then_indexed_descent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (edge : EdgeValue Symbol Guard)
    (inherited : EqValue) (index : Nat)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (stored : Stored before) (active : ActiveExcept bound nodeSkip edgeSkip before) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory
        edge.entry.key.constraint inherited before.checked combined ∧
      SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory
        (prefixState before edge inherited) combined index ∧
      Post formulas solver inventory before (descend (prefixState before edge inherited) combined index).2 memos ∧
      Stored (descend (prefixState before edge inherited) combined index).2 ∧
      ActiveExcept bound nodeSkip edgeSkip (descend (prefixState before edge inherited) combined index).2 := by
  obtain ⟨combined, first, firstPost, firstStored, firstActive⟩ :=
    SourceCurrentAllocatedPartialPlainPrefixes.inherited_prefix formulas solver inventory before memos initial
      edge inherited resident inheritedReady stored active
  obtain ⟨second, secondPost, secondStored, secondActive⟩ :=
    SourceCurrentAllocatedPartialPlainPrefixes.descent formulas solver inventory _ memos firstPost.context
      combined index first.combinedReady firstStored firstActive
  exact ⟨combined, first, second, firstPost.trans secondPost, secondStored, secondActive⟩

theorem parent_satisfaction_enters_literal_child
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (edge : EdgeValue Symbol Guard)
    (inherited : EqValue) (index : Nat)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (stored : Stored before) (active : ActiveExcept bound nodeSkip edgeSkip before) :
    ∃ combined,
      Post formulas solver inventory before (descend (prefixState before edge inherited) combined index).2 memos ∧
      ∀ (symbol : Symbol) (terms : List (Term Symbol)) (term : Term Symbol), terms[index]? = some term →
        SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload →
        SourceEqualityGuardReadback.Sat (.node symbol terms) (SourceCompactGuards.sourceEqualities edge.entry.key.constraint) →
        SourceEqualityPrecheck.Sat term (descend (prefixState before edge inherited) combined index).1.payload := by
  obtain ⟨combined, first, second, post, _, _⟩ :=
    resident_prefix_then_indexed_descent formulas solver inventory before memos initial edge inherited index
      resident inheritedReady stored active
  refine ⟨combined, post, ?_⟩
  intro symbol terms term found inheritedSat ownSat
  exact SourceCurrentAllocatedPartialDescent.parent_satisfied formulas solver inventory _ combined index second
    first.combinedReady symbol terms term found ((first.exact _).mpr ⟨inheritedSat, ownSat⟩)

omit [DecidableEq (EdgeKey Symbol Guard)] in
theorem prefix_and_descent_keep_all_caller_tables
    (before : Caller width) (edge : EdgeValue Symbol Guard) (inherited combined : EqValue) (index : Nat) :
    let after := (descend (prefixState before edge inherited) combined index).2
    after.checked.native = before.checked.native ∧ after.nodeResults = before.nodeResults ∧
      after.edgeResults = before.edgeResults ∧ after.merge = before.merge ∧ after.fourth = before.fourth :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end PlainPrefixesChecks

#print axioms PlainPrefixesChecks.resident_prefix_then_indexed_descent
#check @PlainPrefixesChecks.resident_prefix_then_indexed_descent
#print axioms PlainPrefixesChecks.parent_satisfaction_enters_literal_child
#check @PlainPrefixesChecks.parent_satisfaction_enters_literal_child
#print axioms PlainPrefixesChecks.prefix_and_descent_keep_all_caller_tables
#check @PlainPrefixesChecks.prefix_and_descent_keep_all_caller_tables
