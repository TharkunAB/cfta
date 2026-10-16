import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames

/-!
# Initial interfaces for constrained finite ordinary recursion

A constructed result retains its own graph, strict reads, and checks.
The bounded interface applies only below an independent natural rank.
The root rank induction must derive that interface. These definitions do
not assert graph existence or supply a future successful body.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Plan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Each node result contains its own physical execution and independent semantic and structural laws. -/
def NodeResult (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat)
    (request : NodeRequest) (before : Caller width) (memos : Memos) : Prop :=
  ∃ result after next final, ∃ actual : NodeCall budget request before result after,
    NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
    Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
    Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result

/-- Smaller calls accept only initial invariants and their rooted reached-machine plan. -/
def Below (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget rank : Nat) : Prop :=
  ∀ {inventory : Inventory} {before : Caller width} {memos : Memos} (request : NodeRequest),
    nodeRank request < rank → Context formulas solver inventory before memos →
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → DNode request.value →
    Stored before → ActiveAbove (nodeRank request) before → Plan budget (.nodeCall request before) →
    NodeResult formulas solver budget request before memos

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRecursionDefs
