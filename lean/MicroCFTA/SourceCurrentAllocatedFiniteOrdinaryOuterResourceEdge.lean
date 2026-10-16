import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes

/-!
# Finite outer edge calls from initial uniform headroom

A literal miss transfers the complete request to its captured owner.
Publication retains the same checked heap and every causal store.
Initial uniform supplies derive that owner's parent capacity.
The same completed call produces its quantitative returned certificate.
No future entry plan or completed body is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove edgeRank)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial caller facts and uniform supplies construct their own exact finite edge-call return. -/
theorem finite (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) (rows arity bound : Nat) (limits : Limits)
    (profile : EdgeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits request.value)
    (heightBound : MergedOrdinaryHeight.edgeHeight request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ EdgeNarrow request.value result ∧ EdgeCertificate request result ∧ EdgeLaw formulas solver request result := by
  have capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.CallCapacity bits budget request before := by
    intro handle owner running started
    obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
      initial inherited resident started
    obtain ⟨same, _ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate
      formulas solver request owner before running handle initial.sound
      initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
    have checked : running.checked = before.checked := by
      simpa only [started] using (beginEdge_components request before).1
    have retained : Stored running := by simpa only [started] using stored.beginEdge request
    exact SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity.complete bits formulas solver inventory current
      good.inherited good.input retained limits rows arity bound (by simpa only [same] using guards)
      (by simpa only [same] using profile) (by simpa only [same] using heightBound)
      (by simpa only [checked] using room.1) (by simpa only [checked] using room.2)
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, _stored, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.finite bits formulas solver budget request initial inherited resident
      domain stored.structural active capacity
  obtain ⟨retained, _narrow, certificate⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_call formulas solver
    reads inventory initial inherited resident domain stored
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrow, certificate, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge
