import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
namespace MicroCFTA.ParentInitialCapacityChecks
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

open SourceCurrentAllocatedFiniteOrdinaryParentCapacity (ParentCapacity)

local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
theorem every_same_cache_load (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (live : contradictory request.value.entry.key.constraint = false) (candidate : Allocated)
    (candidateFound : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some candidate)) :
    SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.LocalCapacity bits budget candidate request.inherited
      request.value.children before.checked before.fourth before.merge := by
  exact SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity.complete formulas solver bits budget request loaded initial found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges live candidate candidateFound

theorem constructed_resident_body (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ result checked savedFourth saved next final,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge) result checked savedFourth saved ∧
      ∃ actual : EdgeBody budget request before result (advance before checked savedFourth saved),
        EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (advance before checked savedFourth saved) final ∧
        Post formulas solver next before (advance before checked savedFourth saved) final := by
  have ranges := SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity.resident_ranges formulas solver bits budget request loaded initial found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  exact SourceCurrentAllocatedParentWorkerActual.resident_finite formulas solver budget request initial inherited resident ranges

#print axioms every_same_cache_load
#check @every_same_cache_load
#print axioms constructed_resident_body
#check @constructed_resident_body
end MicroCFTA.ParentInitialCapacityChecks
