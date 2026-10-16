import MicroCFTA.SourceCurrentAllocatedPartialPlainEdgeCall
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
import MicroCFTA.SourceCurrentAllocatedPartialActual

/-!
# Initial-fact interfaces for current plain node recursion

Completed node results retain their own execution and all state effects.
The bounded induction hypothesis applies only to strictly smaller ranks.
These definitions do not assert that the induction hypothesis holds.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A constructed node call retains its own reads, checks, state, and language law. -/
def NodeResult (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat)
    (request : NodeRequest) (before : Caller width) (memos : Memos) : Prop :=
  ∃ result after next final, ∃ actual : NodeCall budget request before result after,
    NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
    Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
    Stored after ∧ NodeLaw formulas solver request result

/-- Smaller-rank calls may use arbitrary initial callers that satisfy the same invariants. -/
def Below (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget rank : Nat) : Prop :=
  ∀ {inventory : Inventory} {before : Caller width} {memos : Memos} (request : NodeRequest),
    nodeRank request < rank → Context formulas solver inventory before memos →
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → SourceEqualityPartialPlainRegion.Region request.value →
    Stored before → ActiveAbove (nodeRank request) before →
    NodeResult formulas solver budget request before memos

end MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs
