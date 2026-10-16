import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall

/-!
# Numeric query-entry plans for actual parent and outer edge calls

Raw rejection requires no local query plan.
A live original field enters the numeric local plan at its actual cache.
An outer miss selects the captured owner before the parent body runs.
Initial caller facts derive each selected entry invariant separately.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove edgeRank)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Only a live loaded original enters its local numeric query plan. -/
def ParentCapacity (bits budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) : Prop :=
  contradictory request.value.entry.key.constraint = false →
    ∀ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
        .ok (some loaded) →
      SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.LocalCapacity bits budget loaded request.inherited
        request.value.children before.checked before.fourth before.merge

/-- Only a newly started captured owner enters its actual parent numeric plan. -/
def CallCapacity (bits budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) : Prop :=
  ∀ handle owner running, beginEdge request before = (handle, .evaluate owner, running) →
    ParentCapacity bits budget owner running

variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Initial resident caller facts derive the existing parent ranges from numeric entries. -/
theorem resident_ranges {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : ParentCapacity bits budget request before) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := by
  intro test loaded found
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  exact SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.ranges bits formulas solver inventory budget
    request.value.entry.key.constraint loaded request.inherited request.value.children before.checked before.fourth before.merge
    initial.ready initial.admitted cached found inherited available domain initial.correct initial.stored initial.covered
    stored.native stored.merge (capacity test loaded found) memos initial.globals

/-- The exact started owner derives readiness and domain before its parent range check. -/
theorem call_ranges {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : CallCapacity bits budget request before) :
    SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.Ranges budget request before := by
  intro handle owner running started
  obtain ⟨current, good, _key, _cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  obtain ⟨_same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate
    formulas solver request owner before running handle initial.sound
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
  have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
  exact resident_ranges bits formulas solver budget owner current good.inherited good.input ownerDomain runningStored
    (capacity handle owner running started)

/-- Numeric entry plans construct finite outer edge execution with the full physical and language return. -/
theorem finite {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) (capacity : CallCapacity bits budget request before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result :=
  SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.finite formulas solver budget request initial inherited resident
    domain stored active (call_ranges bits formulas solver budget request initial inherited resident domain stored capacity)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity
