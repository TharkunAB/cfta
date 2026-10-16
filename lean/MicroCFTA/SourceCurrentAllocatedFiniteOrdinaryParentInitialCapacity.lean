import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity

/-!
# Parent entry capacity from initial constructor resources

Initial resident caller facts derive the local capacity plan.
Every loaded value is read from the same initial equality cache.
Load injectivity identifies it with the initial budget's stored field.
No parent completion or future capacity is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity
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

/-- Initial parent profiles and total headroom derive the existing parent capacity plan. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    ParentCapacity bits budget request before := by
  intro test candidate candidateFound
  have same : candidate = loaded := Option.some.inj (Except.ok.inj (candidateFound.symm.trans found))
  subst candidate
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  exact SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.complete formulas solver inventory bits budget
    request.value.entry.key.constraint loaded request.inherited request.value.children before.checked before.fourth before.merge
    initial.ready initial.admitted cached found inherited available initial.correct initial.stored profiles native output
    initial.covered memos initial.globals rows arity count depth bound profile lengthBound pathsBound heightBound
    (by simpa only [nodeBudget, test, Bool.false_eq_true, ↓reduceIte] using nodes)
    (by simp only [edgeBudget, test, Bool.false_eq_true, ↓reduceIte] at edges; omega)

/-- The derived parent plan supplies the old full ranges at every same-cache loaded field. -/
theorem resident_ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := by
  have capacity := complete formulas solver bits budget request loaded initial found inherited resident profiles native output
    rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  intro test candidate candidateFound
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  exact SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.ranges bits formulas solver inventory budget
    request.value.entry.key.constraint candidate request.inherited request.value.children before.checked before.fourth before.merge
    initial.ready initial.admitted cached candidateFound inherited available (ChildrenShape.domain request.value.children profile)
    initial.correct initial.stored initial.covered native profiles.domain (capacity test candidate candidateFound) memos initial.globals

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity
