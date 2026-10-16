import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScan
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Derived Scan-only checks for finite ordinary input records

Every primary class returns false at the same heap. The existing range
plan therefore reaches no secondary gate, seeded query, or fourth memo.
The local precheck changes only equality operations and retains this fact.
Resident edge records derive the corresponding actual leaf checks.
These results do not supply class target or leaf query capacity.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Initial coherent available domain records derive the complete existing Scan range plan. -/
theorem scan_ranges (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (fourth : Fourth)
    (coherent : InternedRecordCoherence.Coherent before.native.machine.heap)
    (available : Values before.native.machine.heap values) (domain : DChildren values) :
    SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before fourth := by
  induction classes with
  | nil => trivial
  | cons paths classes ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro heap primary
        have same := (SourceCurrentAllocatedFiniteOrdinaryScan.primary_class_verified unconstrained reaches primary
          coherent available domain).2
        subst heap
        simpa only [SourceCurrentAllocatedFiniteOrdinaryScan.advanceHeap_self] using ih
      · intro heap primary
        have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.primary_class_verified unconstrained reaches primary
          coherent available domain).1
        cases impossible
      · intro heap primary
        have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.primary_class_verified unconstrained reaches primary
          coherent available domain).1
        cases impossible

/-- Literal precheck allocation needs no additional Scan checks at its unchanged native heap. -/
theorem local_ranges (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth)
    (coherent : InternedRecordCoherence.Coherent before.native.machine.heap)
    (available : Values before.native.machine.heap values) (domain : DChildren values) :
    SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth := by
  intro records _actual
  exact scan_ranges budget sourceGate sourceReaches values (records.map SourceEqualityClassOrder.Record.paths)
    (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth coherent available domain

/-- Current resident domain edges derive every live-load Scan check used by actual body verification. -/
theorem resident_ranges (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) :
    SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before := by
  intro _live loaded _found
  exact local_ranges budget loaded request.inherited request.value.children before.checked before.fourth
    semantic.ready.semantic.1.normal.facts.coherent
    (semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident) domain

/-- An actual parent body has its own Scan-only Checks from initial resident domain records. -/
theorem edge_body_checks {budget : Nat} {request : EdgeRequest} {before after : Caller width}
    {result : EdgeValue Symbol Guard} (actual : EdgeBody budget request before result after)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) :
    Checks (edgeBodyTrace actual) :=
  SourceCurrentAllocatedPartialChecksComposition.edge_body actual (resident_ranges budget request before semantic resident domain)

/-- Exact captured-owner transport derives actual completed edge-call checks without a future range plan. -/
theorem edge_call_checks
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest} {before after : Caller width}
    {result : EdgeValue Symbol Guard} {memos : Memos} (actual : EdgeCall budget request before result after)
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) :
    Checks (edgeCallTrace actual) := by
  cases actual with
  | hit started => exact SourceCurrentAllocatedPartialChecksComposition.edge_hit started
  | evaluate started body =>
      obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
        initial inherited resident started
      have ownerDomain := (SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver request _ before _ _
        initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started).2.1
      exact SourceCurrentAllocatedPartialChecksComposition.edge_evaluate started body
        (edge_body_checks body current.ready.semantic good.input ownerDomain)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges
