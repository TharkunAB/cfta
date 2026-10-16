import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual
namespace FiniteOrdinaryScanRangeKernels
open MicroCFTA Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Existing finite Scan completion needs no supplied machine range plan on the finite ordinary domain. -/
theorem completed_scan (budget : Nat)
    (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (fourth : Fourth)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    ∃ _actual : SourceCurrentConjunctionClassScan.Scan budget unconstrained reaches values classes before fourth
        none classes before fourth,
      SourceCurrentConjunctionClassScan.Ready before ∧ Values before.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth := by
  obtain ⟨outcome, selected, after, saved, actual, finalReady, _effects, finalValues, finalCorrect, _retained⟩ :=
    SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches values classes
      before fourth ready available proper correct
      (SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget unconstrained reaches values classes before fourth
        ready.good.native.machine.1.coherent available domain)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.scan actual ready available domain
  exact ⟨actual, finalReady, finalValues, finalCorrect⟩

/-- Actual strict parent-body reads derive their full semantic and structural return without any range input. -/
theorem parent_body_verified
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest} {before after : Caller width}
    {result : EdgeValue Symbol Guard} {memos final : Memos}
    {actual : EdgeBody budget request before result after}
    (reads : EdgeBodyReads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before) :
    Checks (edgeBodyTrace actual) ∧
      ∃ next, Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ EdgeNarrow request.value result ∧
        SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryScanRanges.edge_body_checks actual initial.ready.semantic resident domain
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.edge_body formulas solver reads
    inventory checks initial inherited resident
  have structural := SourceCurrentAllocatedFiniteOrdinaryOuterActual.edge_body formulas solver reads
    inventory checks initial inherited resident domain stored
  exact ⟨checks, next, post, output, structural.1, structural.2, law⟩
end FiniteOrdinaryScanRangeKernels
#print axioms FiniteOrdinaryScanRangeKernels.completed_scan
#check @FiniteOrdinaryScanRangeKernels.completed_scan
#print axioms FiniteOrdinaryScanRangeKernels.parent_body_verified
#check @FiniteOrdinaryScanRangeKernels.parent_body_verified
