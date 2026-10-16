import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterAdmission
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode

namespace MicroCFTA.OuterAdmissionKernels
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Step Reach)
open SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries (Plan Admitted)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem numeric_node_constructs (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node request.value) (stored : Stored before)
    (active : SourceCurrentAllocatedPartialActiveOrder.ActiveAbove (SourceCurrentAllocatedPartialActiveOrder.nodeRank request) before)
    (plan : Plan bits budget (.nodeCall request before)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialChecks.Checks (SourceCurrentAllocatedPartialChecks.nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow request.value result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  have admitted : Admitted formulas solver (.nodeCall request before) :=
    ⟨inventory, memos, initial, stored, inherited, available, domain⟩
  exact SourceCurrentAllocatedFiniteOrdinaryOuterNode.finite formulas solver budget request initial inherited available
    domain stored active (SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.ranges bits formulas solver admitted plan)

theorem row_suffix_admitted (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {original narrowed result : EdgeValue Symbol Guard} {originals : List (EdgeValue Symbol Guard)}
    {before middle afterChildren : Caller (bits + 2)}
    (initial : Admitted formulas solver (.rows inherited (original :: originals) before))
    (plan : Plan bits budget (.rows inherited (original :: originals) before))
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result afterChildren) :
    Admitted formulas solver (.rows inherited originals afterChildren) ∧
      SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget (.rows inherited originals afterChildren) := by
  have reached : Reach budget (.rows inherited (original :: originals) before) (.rows inherited originals afterChildren) :=
    .direct (.rows_tail edge children)
  have admitted := SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.reach bits formulas solver reached initial plan
  exact ⟨admitted, SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.ranges bits formulas solver admitted (plan.restrict reached)⟩

theorem indexed_suffix_admitted (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {combined : SourceEqualityConstraintAllocation.Value} {index : Nat}
    {value result : Node} {values : List Node} {before middle : Caller (bits + 2)}
    (initial : Admitted formulas solver (.walk combined index (value :: values) before))
    (plan : Plan bits budget (.walk combined index (value :: values) before))
    (earlier : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle) :
    Admitted formulas solver (.walk combined (index + 1) values middle) ∧
      SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget (.walk combined (index + 1) values middle) := by
  have reached : Reach budget (.walk combined index (value :: values) before) (.walk combined (index + 1) values middle) :=
    .direct (.walk_tail earlier)
  have admitted := SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.reach bits formulas solver reached initial plan
  exact ⟨admitted, SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.ranges bits formulas solver admitted (plan.restrict reached)⟩

#check @numeric_node_constructs
#print axioms numeric_node_constructs
#check @row_suffix_admitted
#print axioms row_suffix_admitted
#check @indexed_suffix_admitted
#print axioms indexed_suffix_admitted
end MicroCFTA.OuterAdmissionKernels
