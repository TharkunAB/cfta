import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds

/-!
# Initial constructor budgets for actual checked operands

An operand projects its captured forest and merges the actual projection.
Initial forest limits bound both operations at their exact returned heaps.
The endpoint constructs the existing full checked receipt before counting it.
No intermediate profile, capacity, completion, or request count is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode (Budget)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "P" => SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.nodeBudget
local notation "E" => SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edgeBudget
local notation "Envelope" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope

/-- Bound the projection root, original node occurrences, and generated Merge requests. -/
def nodeBudget (rows arity count depth bound : Nat) : Nat :=
  1 + count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound +
    N (P rows count depth) arity bound

/-- Projection emits no edge request; Merge uses its generated input profile. -/
def edgeBudget (rows arity count depth bound : Nat) : Nat := E (P rows count depth) arity bound

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem merge_counted {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedMerge.Merge clear input before memo output after saved)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (available : Available before.native.machine.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    Profiles saved ∧ NodeShape (Envelope rows bound) arity output ∧ height output ≤ bound ∧
      Budget before.native.machine.heap after.native.machine.heap (N rows arity bound) (E rows arity bound) := by
  cases actual with
  | done call =>
      have counted := SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer.call_budget call.graph
        ready.semantic ready.costs physical profiles available
      have outputProfile := counted.2.2.2.1.2 rows arity bound profile heightBound
      exact ⟨counted.2.2.1, outputProfile.1, Nat.le_trans outputProfile.2 heightBound,
        counted.2.2.2.2 rows arity bound profile heightBound⟩

/-- Initial forest bounds construct the full operand receipt and its cumulative constructor trace. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    ∃ output after saved final requests,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output after saved memos final ∧
      Profiles saved ∧ NodeShape (Envelope (P rows count depth) bound) arity output ∧ height output ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget rows arity count depth bound ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget rows arity count depth bound := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.domain values profile
  have selected := SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain path
  obtain ⟨output, after, saved, final, receipt⟩ := SourceCurrentAllocatedMergeOperand.complete
    formulas solver inventory path values before memo ready admitted available selected physical covered memos valid
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have produced := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forest_uniform projection.graph
    ready.semantic available profile count depth bound lengthBound pathBound heightBound
  obtain ⟨earlier, firstTrace, firstNodes, firstEdges, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.forest projection.graph ready.semantic available domain
  obtain ⟨finalProfiles, finalProfile, finalHeight, later, lastTrace, lastNodes, lastEdges⟩ :=
    merge_counted merged.actual projection.ready (physical.grows projection.effects.keeps) profiles projection.available
      (P rows count depth) arity bound produced.1 produced.2
  have originalCounts := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
  have originalNodes := Nat.le_trans originalCounts.1
    (Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound) lengthBound)
  have trace : Trace before.native.machine.heap after.native.machine.heap (earlier ++ later) := .trans firstTrace lastTrace
  have nodes : nodeRequests (earlier ++ later) ≤ nodeBudget rows arity count depth bound := by
    rw [nodeRequests_append]
    unfold nodeBudget
    omega
  have edges : edgeRequests (earlier ++ later) ≤ edgeBudget rows arity count depth bound := by
    rw [edgeRequests_append, firstEdges]
    simpa only [edgeBudget, Nat.zero_add] using lastEdges
  have supplies := trace.next_le
  exact ⟨output, after, saved, final, earlier ++ later, receipt, finalProfiles, finalProfile,
    finalHeight, trace, nodes, edges, by omega, by omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandResources
