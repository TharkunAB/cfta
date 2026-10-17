import MicroCFTA.SourceCurrentConstrainedCapStaticQueries

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000

namespace MicroCFTA.StaticQueriesIndependentIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Native" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "Current" => SourceCurrentAllocatedRecursivePrefixState.Current
local notation "domains" => SourceRecursiveIntersectionSourceInventory.domains
local notation "Receipt" => SourceCurrentAllocatedTargetQuery.Receipt
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial counters construct both literal returns and pay the fixed domain inventory only once. -/
theorem two_initial_queries (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before) (native : Native before)
    (left right nextLeft nextRight : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (nextLeftAvailable : Available before.native.machine.heap nextLeft)
    (nextRightAvailable : Available before.native.machine.heap nextRight)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nextLeftClosed : nextLeft.free = []) (nextRightClosed : nextRight.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right)
    (nextLeftCap : Cap Plain depth nextLeft) (nextRightCap : Cap Plain depth nextRight)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
      2 ^ (bits + 1)) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ first result middle after firstInventory finalInventory,
      Receipt formulas solver firstInventory left right before first middle memos ∧
      Receipt formulas solver finalInventory nextLeft nextRight middle result after memos ∧
      SourceCurrentConstrainedCapStaticQueries.Queries formulas solver memos
        [(left, right), (nextLeft, nextRight)] before [first, result] after ∧
      Current before.native.machine.heap (domains before.native.machine.heap) before.native.machine.domains middle ∧
      Current before.native.machine.heap (domains before.native.machine.heap) before.native.machine.domains after ∧
      Native after ∧ Cap Plain depth first ∧ Cap Plain depth result ∧
      Extension before.native.machine after.native.machine ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      Valid after.native.machine.heap memos ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next +
        2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) ∧
      after.native.machine.domains.next < 2 ^ (bits + 1) := by
  have reserved := SourceCurrentConstrainedCapStaticQueries.resources ready.good.native.machine.1
    ready.good.native.machine.2 nodes edges room
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial before.native.machine.heap
    (domains before.native.machine.heap) before ready.good ready.semantic rfl
  obtain ⟨firstInventory, first, middle, firstReceipt, firstCurrent, firstNative, firstCap⟩ :=
    SourceCurrentConstrainedCapStaticQueries.complete depth reserved formulas solver inventory before
      ready admitted initial native left right leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap memos valid
  obtain ⟨finalInventory, result, after, nextReceipt, finalCurrent, finalNative, finalCap⟩ :=
    SourceCurrentConstrainedCapStaticQueries.complete depth reserved formulas solver firstInventory middle
      firstReceipt.ready firstReceipt.admitted firstCurrent firstNative nextLeft nextRight nextLeftAvailable nextRightAvailable
      nextLeftClosed nextRightClosed nextLeftCap nextRightCap memos firstReceipt.globals
  have bound : after.native.machine.domains.next ≤ before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) := by
    simpa only [SourceRecursiveIntersectionSourceInventory.domains_length] using finalCurrent.domains.next_le
  exact ⟨first, result, middle, after, firstInventory, finalInventory, firstReceipt, nextReceipt,
    .cons firstReceipt (.cons nextReceipt .nil), firstCurrent, finalCurrent, finalNative, firstCap, finalCap,
    firstReceipt.extension.trans nextReceipt.extension, firstReceipt.effects.operations.trans nextReceipt.effects.operations,
    nextReceipt.globals, bound, Nat.lt_of_le_of_lt bound room⟩

end MicroCFTA.StaticQueriesIndependentIntegration

#print axioms MicroCFTA.StaticQueriesIndependentIntegration.two_initial_queries
#check @MicroCFTA.StaticQueriesIndependentIntegration.two_initial_queries
