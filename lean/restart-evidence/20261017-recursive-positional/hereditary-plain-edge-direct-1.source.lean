import MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainEdge
import MicroCFTA.SourceCurrentHereditaryUnconstrained

/-!
# Actual plain edge calls from local hereditary row annotations

Resident children and their closed local annotations derive the traversed
plain Region. Other heap records and outer owners remain unrestricted.
The finite endpoint constructs its own execution and full caller receipt.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialHereditaryPlainEdge
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove PlainEdge)
open SourceCurrentAllocatedPartialActiveOrder (edgeRank)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable {width : Nat}

private theorem children_of_regions (values : List (Value Symbol Guard))
    (regions : ∀ value ∈ values, SourceEqualityPartialPlainRegion.Region value) :
    SourceEqualityPartialPlainRegion.Children values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (regions value List.mem_cons_self)
        (ih (fun value member => regions value (List.mem_cons_of_mem _ member)))

/-- Local closed annotations and actual resident children derive the filtered plain-edge predicate. -/
theorem plain_edge (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (edge : Edge) (resident : EdgeResident state edge)
    (annotated : SourceCurrentHereditaryConstructors.Edge plain edge)
    (closed : MergedColdReaderClosedInputs.ClosedValues edge.children) : PlainEdge edge := by
  refine ⟨SourceCurrentHereditaryUnconstrained.plain_equalities _ annotated.1, ?_⟩
  apply children_of_regions
  intro child member
  exact SourceCurrentHereditaryUnconstrained.to_plain_region state facts child
    (annotated.2 child member) (facts.cached.edges edge.entry.key edge resident child member) (closed child member)

/-- A locally hereditary resident row constructs a finite mixed-cache edge call and its same-state receipt. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (annotated : SourceCurrentHereditaryConstructors.Edge plain request.value)
    (closed : MergedColdReaderClosedInputs.ClosedValues request.value.children)
    (stored : Stored before) (active : ActiveAbove (edgeRank request) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ Shape request.value result ∧ EdgeLaw formulas solver request result :=
  SourceCurrentAllocatedPartialConditionalPlainEdge.finite formulas solver budget request initial inherited resident
    (plain_edge before.checked.native.machine.heap initial.ready.semantic.ready.semantic.1.normal.facts
      request.value resident annotated closed) stored active

end MicroCFTA.SourceCurrentAllocatedPartialHereditaryPlainEdge
