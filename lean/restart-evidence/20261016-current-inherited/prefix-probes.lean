import MicroCFTA.SourceCurrentAllocatedInheritedPrefix
import MicroCFTA.SourceCurrentAllocatedMkEdge

namespace MicroCFTA.SourceCurrentAllocatedInheritedPrefix
open Language InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready

#print axioms run
#print axioms run_contradiction
#print axioms run_error
#print axioms run_missing
#print axioms run_combine
#print axioms state
#print axioms state_native
#print axioms state_operations
#print axioms state_contradiction
#print axioms Receipt
#print axioms contradiction
#print axioms finite
#print axioms resident_finite
#print axioms Receipt.guard_satisfied

#check @run
#check @run_contradiction
#check @run_error
#check @run_missing
#check @run_combine
#check @state
#check @state_native
#check @state_operations
#check @state_contradiction
#check @Receipt
#check @contradiction
#check @finite
#check @resident_finite
#check @Receipt.guard_satisfied

variable {width : Nat}

/-- An arbitrary unavailable or malformed own field is not read under inherited contradiction. -/
theorem kernel_short_skip (original : Guard) (operations : Operations) :
    run original .contradiction operations = (.ok (some .contradiction), operations) :=
  run_contradiction original operations

/-- A reached error retains its actual state and prevents combination. -/
theorem kernel_error (original : Guard) (identity : Nat) (records : List SourceEqualityClassOrder.Record)
    (before : Operations) (message : String)
    (failed : (SourceCurrentConjunctionEquality.accessor original before).1 = .error message) :
    run original (.live identity records) before =
      (.error message, (SourceCurrentConjunctionEquality.accessor original before).2) :=
  run_error original identity records before message failed

/-- A missing field is retained separately from an error and contradiction. -/
theorem kernel_missing (original : Guard) (identity : Nat) (records : List SourceEqualityClassOrder.Record)
    (before : Operations)
    (missing : (SourceCurrentConjunctionEquality.accessor original before).1 = .ok none) :
    run original (.live identity records) before =
      (.ok none, (SourceCurrentConjunctionEquality.accessor original before).2) :=
  run_missing original identity records before missing

/-- Initial readiness derives a contradiction receipt without a field or inherited-value receipt. -/
theorem kernel_contradiction (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Guard) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before) :
    Receipt formulas solver inventory original .contradiction before .contradiction ∧
      state before original .contradiction = before :=
  ⟨contradiction formulas solver inventory original before ready admitted, state_contradiction before original⟩

/-- Both actual native memo families and the domain cache are retained literally. -/
theorem kernel_native_tables (original : Guard) (inherited : EqValue) (before : Checked width) :
    (state before original inherited).native.nodes = before.native.nodes ∧
      (state before original inherited).native.edges = before.native.edges ∧
      (state before original inherited).native.machine.domains = before.native.machine.domains ∧
      (state before original inherited).native.machine.heap = before.native.machine.heap :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Residency supplies the actual available field; no future load is a premise. -/
theorem kernel_resident (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (edge : EdgeValue Symbol Guard) (inherited : EqValue) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap edge)
    (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ combined, (run edge.entry.key.constraint inherited before.operations).1 = .ok (some combined) ∧
      Ready (state before edge.entry.key.constraint inherited) ∧
      At formulas solver inventory (state before edge.entry.key.constraint inherited) := by
  obtain ⟨combined, receipt⟩ := resident_finite formulas solver inventory edge inherited before
    ready admitted resident inheritedReady
  exact ⟨combined, receipt.actual, receipt.ready, receipt.admitted⟩

/-- Actual guard acceptance and inherited satisfaction produce the combined parent's obligations. -/
theorem kernel_parent_sat
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {original : Guard} {inherited combined : EqValue} {before : Checked width}
    (receipt : Receipt formulas solver inventory original inherited before combined) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true)
    (inheritedSat : SourceEqualityPrecheck.Sat term inherited.payload) :
    SourceEqualityPrecheck.Sat term combined.payload := receipt.guard_satisfied term accepted inheritedSat

/-- The exact returned operation cache supports actual indexed descent and child satisfaction. -/
theorem kernel_actual_descend
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {original : Guard} {inherited combined : EqValue} {before : Checked width}
    (receipt : Receipt formulas solver inventory original inherited before combined)
    (symbol : Symbol) (terms : List (Term Symbol)) (index : Nat) (childTerm : Term Symbol)
    (selected : terms[index]? = some childTerm)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true)
    (inheritedSat : SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload) :
    let actual := SourceEqualityConstraintMemoAllocation.descend combined index
      (state before original inherited).operations
    SourceEqualityConstraintMemoAllocation.Valid actual.2 ∧ EqReady actual.2.constraints actual.1 ∧
      SourceEqualityPrecheck.Sat childTerm actual.1.payload ∧
      SourceEqualityConstraintMemoAllocation.Grows (state before original inherited).operations actual.2 := by
  have descended := SourceEqualityConstraintMemoAllocation.descend_correct combined index
    (state before original inherited).operations receipt.valid receipt.combinedReady
  refine ⟨descended.1, descended.2.1, ?_, descended.2.2.2⟩
  rw [descended.2.2.1]
  exact SourceEqualityDescend.descend_sound combined.payload receipt.combinedReady.2 symbol terms index childTerm
    selected (receipt.guard_satisfied (.node symbol terms) accepted inheritedSat)

/-- Actual combined contradiction rules out simultaneous full-guard and inherited acceptance. -/
theorem kernel_combined_rejection
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {original : Guard} {inherited : EqValue} {before : Checked width}
    (receipt : Receipt formulas solver inventory original inherited before .contradiction) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true) :
    ¬ SourceEqualityPrecheck.Sat term inherited.payload := by
  intro inheritedSat
  exact receipt.guard_satisfied term accepted inheritedSat

/-- A checked sentinel supplies its returned Top field at the actual grown state. -/
theorem kernel_returned_sentinel [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {symbol : Symbol} {before after : Checked width} {edge : EdgeValue Symbol Guard}
    (constructor : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before edge after)
    (inherited : EqValue) (inheritedReady : EqReady after.operations.constraints inherited) :
    edge.children = [.empty] ∧ edge.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧
      ∃ combined, Receipt formulas solver inventory edge.entry.key.constraint inherited after combined :=
  ⟨constructor.children, constructor.guard, resident_finite formulas solver inventory edge inherited after
    constructor.ready constructor.admitted constructor.resident inheritedReady⟩

end MicroCFTA.SourceCurrentAllocatedInheritedPrefix
