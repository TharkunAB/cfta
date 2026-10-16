import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity

/-!
# Initial resource interface for ordinary outer recursion

Headroom bounds the remaining constructor supply before execution.
Completed actual Work transfers that bound to the next caller.
The induction interface applies only to smaller original node ranks.
It assumes no completion or future entry plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers (nodeNodes nodeEdges)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node

/-- Both initial supplies cover the stated remaining constructor requests. -/
def Headroom (bits : Nat) (heap : Heap) (nodes edges : Nat) : Prop :=
  heap.nodes.next + nodes ≤ 2 ^ bits ∧ heap.edges.next + edges ≤ 2 ^ (bits + 2)

/-- A smaller reservation follows from the same initial supply. -/
theorem Headroom.mono {bits : Nat} {heap : Heap} {nodes edges smallNodes smallEdges : Nat}
    (room : Headroom bits heap nodes edges) (nodeBound : smallNodes ≤ nodes) (edgeBound : smallEdges ≤ edges) :
    Headroom bits heap smallNodes smallEdges := by
  rcases room with ⟨nodes, edges⟩
  constructor <;> omega

section
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The exact completed prefix leaves the reserved suffix supply available. -/
theorem Headroom.after {bits : Nat} {before after : Heap} {usedNodes usedEdges restNodes restEdges : Nat}
    (room : Headroom bits before (usedNodes + restNodes) (usedEdges + restEdges))
    (work : WorkBounds before after usedNodes usedEdges) : Headroom bits after restNodes restEdges := by
  obtain ⟨requests, trace, nodes, edges⟩ := work
  have growth := trace.next_le
  rcases room with ⟨nodeRoom, edgeRoom⟩
  constructor <;> omega
end

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A constructed node result retains its graph, reads, semantics, and all causal stores. -/
def NodeResult (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat)
    (request : NodeRequest) (before : Caller (bits + 2)) (memos : Memos) : Prop :=
  ∃ result after next final, ∃ actual : NodeCall budget request before result after,
    NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
    Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
    Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result

/-- Smaller calls use current input profiles and initial headroom alone. -/
def Below (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget rank : Nat) : Prop :=
  ∀ {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos} (request : NodeRequest),
    nodeRank request < rank → Context formulas solver inventory before memos →
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → DNode request.value →
    Stored before → ActiveAbove (nodeRank request) before → ∀ rows arity bound (limits : Limits),
    NodeShape rows arity request.value → SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value →
    MergedOrdinaryHeight.height request.value ≤ bound →
    Headroom bits before.checked.native.machine.heap (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) →
    NodeResult bits formulas solver budget request before memos

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs
