import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources

namespace TargetQueryIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
local notation "Receipt" => SourceCurrentAllocatedTargetQuery.Receipt
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial total headroom constructs two full queries, including a query of the first produced value. -/
theorem two_generated_queries (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (bits rows arity bound : Nat) (left right : Value Symbol Guard) (before : Checked (bits + 2))
    (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (stored : Stored before.native) (outputStored : OutputStored before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : before.native.machine.heap.nodes.next +
      (N rows arity bound + N (rows * rows) (max arity 1) bound) ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next +
      (N rows arity bound + N (rows * rows) (max arity 1) bound) ≤ 2 ^ (bits + 2))
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ middleInventory finalInventory firstValue output middle after requests,
      Receipt formulas solver middleInventory left right before firstValue middle memos ∧
      Receipt formulas solver finalInventory firstValue firstValue middle output after memos ∧
      Stored after.native ∧ OutputStored after.native ∧
      NodeShape ((rows * rows) * (rows * rows)) (max (max arity 1) 1) output ∧ Capacity bits after ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests + edgeRequests requests ≤ N rows arity bound + N (rows * rows) (max arity 1) bound ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next +
        (N rows arity bound + N (rows * rows) (max arity 1) bound) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next +
        (N rows arity bound + N (rows * rows) (max arity 1) bound) ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient output term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term := by
  obtain ⟨middleInventory, firstValue, middle, firstRequests, first, firstStored, firstOutput, firstShape,
      firstLeftHeight, _firstRightHeight, firstTrace, firstCount, _firstCapacity, firstNodes, firstEdges⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources.finite formulas solver inventory bits rows arity bound
      left right before ready admitted stored outputStored leftAvailable rightAvailable leftClosed rightClosed
      leftShape rightShape heights (by omega) (by omega) memos valid
  have firstHeight : height firstValue ≤ bound :=
    Nat.le_trans firstLeftHeight (Nat.le_trans (Nat.le_max_left _ _) heights)
  obtain ⟨finalInventory, output, after, lastRequests, last, lastStored, lastOutput, lastShape,
      _lastLeftHeight, _lastRightHeight, lastTrace, lastCount, lastCapacity, lastNodes, lastEdges⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources.finite formulas solver middleInventory bits
      (rows * rows) (max arity 1) bound firstValue firstValue middle first.ready first.admitted
      firstStored firstOutput first.available first.available first.closed first.closed firstShape firstShape
      (by simpa only [Nat.max_self] using firstHeight) (by omega) (by omega) memos first.globals
  have totalTrace : Trace before.native.machine.heap after.native.machine.heap (firstRequests ++ lastRequests) :=
    firstTrace.trans lastTrace
  have totalCount : nodeRequests (firstRequests ++ lastRequests) + edgeRequests (firstRequests ++ lastRequests) ≤
      N rows arity bound + N (rows * rows) (max arity 1) bound := by
    rw [nodeRequests_append, edgeRequests_append]
    omega
  refine ⟨middleInventory, finalInventory, firstValue, output, middle, after, firstRequests ++ lastRequests,
    first, last, lastStored, lastOutput, lastShape, lastCapacity, totalTrace, totalCount, by omega, by omega, ?_⟩
  intro ambient term
  constructor
  · intro accepted
    exact (first.meaning ambient term).mp ((last.meaning ambient term).mp accepted).1
  · intro accepted
    have firstAccepted := (first.meaning ambient term).mpr accepted
    exact (last.meaning ambient term).mpr ⟨firstAccepted, firstAccepted⟩

end TargetQueryIntegration

#check @TargetQueryIntegration.two_generated_queries
#print axioms TargetQueryIntegration.two_generated_queries
