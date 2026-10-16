import MicroCFTA.SourceCurrentAllocatedPrecheck

#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.state_native
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.state_operations
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.loaded_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.complete
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.resident_complete
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.own_exact
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.own_accepted
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.combined_exact
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.unchanged
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.empty_excludes
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.empty_guard
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.classes
#print axioms MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.classes_exact
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.state_native
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.state_operations
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.loaded_complete
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.complete
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.resident_complete
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.own_exact
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.own_accepted
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.combined_exact
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.unchanged
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.empty_excludes
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.empty_guard
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.classes
#check @MicroCFTA.SourceCurrentAllocatedPrecheck.Receipt.classes_exact

namespace MicroCFTA.CheckedPrecheckProbe
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPrecheck
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inventory : Inventory) (original : Guard) (loaded : Allocated) (inherited own : EqValue)
variable (before : Checked width) (branch : SourceEqualityPrecheck.Branch)
variable (receipt : Receipt formulas solver inventory original loaded inherited before own branch)

-- A resident current edge supplies its field load and warm checked precheck.
example (ready : Ready before) (admitted : At formulas solver inventory before)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited) :
    ∃ loaded own branch, Receipt formulas solver inventory edge.entry.key.constraint loaded inherited before own branch ∧
      Ready (state before loaded inherited) ∧ At formulas solver inventory (state before loaded inherited) ∧
      (state before loaded inherited).native = before.native := by
  obtain ⟨loaded, own, branch, actual⟩ := resident_complete formulas solver inventory before ready admitted edge resident inherited inheritedReady
  exact ⟨loaded, own, branch, actual, actual.ready, actual.admitted, state_native before loaded inherited⟩

-- The complete native tables, domain cache, and literal equality prefix are retained together.
example :
    (state before loaded inherited).native.nodes = before.native.nodes ∧
    (state before loaded inherited).native.edges = before.native.edges ∧
    (state before loaded inherited).native.machine.domains = before.native.machine.domains ∧
    (state before loaded inherited).operations =
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2 :=
  ⟨rfl, rfl, rfl, rfl⟩

-- A true full original guard plus inherited obligations cannot reach rejected children.
example (same : branch = .emptyChildren) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true)
    (inheritedSat : SourceEqualityPrecheck.Sat term inherited.payload) : False :=
  receipt.empty_guard same term accepted inheritedSat

-- Live ordered records retain every class satisfied by the full original guard.
example (output : List SourceEqualityClassOrder.Record) (same : branch = .classes output) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true) :
    Satisfies term (output.map SourceEqualityClassOrder.Record.paths) :=
  (receipt.classes_exact output same term).mpr (SourceEqualityPCSGuard.own_sat formulas solver original term accepted)

-- An unchanged equality prefix imposes no equality obligation; the raw guard remains separate.
example (same : branch = .unchanged) (term : Term Symbol) :
    SourceEqualityPrecheck.Sat term own.payload ∧ SourceEqualityPrecheck.Sat term inherited.payload := by
  have empty := receipt.unchanged same
  simp only [empty.1, empty.2.1, SourceEqualityPrecheck.Sat, Satisfies, List.map_nil, List.not_mem_nil, false_implies, implies_true, and_self]

-- Every earlier successful field load survives the actual returned operation cache.
example (other : Guard) (value : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load other before.operations.constraints = .ok (some value)) :
    SourceEqualityConstraintFieldLookup.load other (state before loaded inherited).operations.constraints = .ok (some value) :=
  SourceCurrentConjunctionEquality.load_grows other before.operations (state before loaded inherited).operations receipt.grows value found

-- Fourth-memo correctness survives the prefix at its unchanged constructor heap.
example (memo : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    SourceCurrentEmptinessMemo.Correct formulas solver (state before loaded inherited).native.machine.heap memo :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps memo correct

-- Existing global memo validity uses the same physical heap, not reset tables.
example (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    EndpointMemoGateTrace.Valid (state before loaded inherited).native.machine.heap memos := valid

end MicroCFTA.CheckedPrecheckProbe
