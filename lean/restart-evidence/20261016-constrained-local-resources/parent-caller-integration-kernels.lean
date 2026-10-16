import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCallerResources
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Parent resources with the full returned outer caller

The initial loaded field selects the numeric budget.
The constructed parent graph supplies the same caller body and strict Reads.
Its receipt retains outer cells, probes, global memos, and the language law.
No future range or capacity plan is an input.
-/
namespace MicroCFTA.ParentCallerResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialState (EdgeRequest advance)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialGraph (EdgeBody)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem constructed_caller_then_scan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    (bits budget : Nat) (request : EdgeRequest) (loaded : Allocated) {before : Caller (bits + 2)}
    {memos : EndpointMemoGateTrace.Memos} (initial : Context formulas solver inventory before memos)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (profiles : Profiles before.merge) (native : NativeStored before.checked.native) (output : OutputStored before.checked.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity request.value.children)
    (lengthBound : request.value.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard request.inherited before.checked.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight request.value.children ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (followup : EqualityNormalize.Constraints) :
    ∃ result checked saved next final requests,
    ∃ actual : EdgeBody budget request before result (advance before checked before.fourth saved),
      EdgeBodyReads formulas solver actual memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result (advance before checked before.fourth saved) final ∧
      Post formulas solver next before (advance before checked before.fourth saved) final ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge) result checked before.fourth saved ∧
      NativeStored checked.native ∧ OutputStored checked.native ∧ Profiles saved ∧
      EdgeShape (outputRows request.value.entry.key.constraint loaded request.inherited before.checked.operations rows count depth bound)
        (outputArity request.value.entry.key.constraint loaded request.inherited before.checked.operations arity count) result ∧
      EdgeNarrow request.value result ∧ Trace before.checked.native.machine.heap checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      Capacity bits checked ∧
      checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      ∃ scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
        (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) result.children followup checked before.fourth
          none followup checked before.fourth,
        SourceCurrentAllocatedScanSourceReads.ScanReads scan final final := by
  obtain ⟨result, checked, saved, next, final, requests, actual, reads, receipt, post, stable, finalNative,
    finalOutput, finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentCallerResources.complete formulas solver bits budget request loaded initial
      found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  have available := post.context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ result receipt.resident
  obtain ⟨scan, scanReads⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.construct budget result.children followup checked
    before.fourth post.context.ready available (EdgeShape.domain result produced) final
  exact ⟨result, checked, saved, next, final, requests, actual, reads, receipt, post, stable, finalNative, finalOutput,
    finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply, scan, scanReads⟩

end MicroCFTA.ParentCallerResourceChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.ParentCallerResourceChecks.constructed_caller_then_scan
#check @MicroCFTA.ParentCallerResourceChecks.constructed_caller_then_scan
