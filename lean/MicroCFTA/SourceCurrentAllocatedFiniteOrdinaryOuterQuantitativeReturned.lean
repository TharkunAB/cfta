import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReturned
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers

/-!
# Quantitative profiles at exact outer returned owners

Each returned cell retains a universal conditional output profile.
The profile uses the complete captured input value.
Publication creates no returned value. Finish requires a derived law.
Warm readback uses coherent complete records before it transfers that law.
These lifecycle results do not assert a producer execution or a root Plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open MergedOrdinaryHeight (height edgeHeight)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers (nodeRows nodeGuards)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
local notation "NodeProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "EdgeProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}

/-- A node certificate includes parent reduction and traversal of returned descendants. -/
def NodeCertificate (owner : NodeRequest) (result : Node) : Prop :=
  ∀ rows arity bound (limits : Limits), NodeShape rows arity owner.value →
    NodeProfile limits owner.value → height owner.value ≤ bound →
    NodeShape (nodeRows rows arity limits bound) (max arity 1) result ∧
      NodeProfile (nodeGuards rows arity limits bound) result

/-- An edge call stores its parent result before the caller traverses descendants. -/
def EdgeCertificate (owner : EdgeRequest) (result : Edge) : Prop :=
  ∀ rows arity bound (limits : Limits), EdgeShape rows arity owner.value →
    EdgeProfile limits owner.value → edgeHeight owner.value ≤ bound →
    EdgeShape (parentRows limits rows arity bound) (max arity 1) result ∧
      EdgeProfile (parentGuards limits) result

/-- Each literal returned cell retains the quantitative law for its captured owner. -/
structure Stored (state : Caller width) : Prop where
  nodes : ∀ handle owner result, state.nodeResults.cells handle = some ⟨owner, .returned result⟩ →
    NodeCertificate owner result
  edges : ∀ handle owner result, state.edgeResults.cells handle = some ⟨owner, .returned result⟩ →
    EdgeCertificate owner result

/-- Empty outer tables derive both certificates over arbitrary lower warm state. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked merge fourth) := by
  constructor <;> intros <;> contradiction

/-- Lower checked advancement retains both complete outer result tables. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth merge) := ⟨stored.nodes, stored.edges⟩

private theorem lookup_returned_before [DecidableEq Key] (key : Key) (request : Request)
    (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.lookupOrInsert key request memo).2 memo := by
  intro handle owner result returned
  cases found : memo.table key with
  | some existing => simpa only [FlatMemoThunk.lookupOrInsert, found] using returned
  | none =>
      by_cases same : handle = memo.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, put] at returned
      · simpa only [FlatMemoThunk.lookupOrInsert, found, put, ite_eq_right same] using returned

private theorem demand_returned_before (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.demand handle memo).2 memo := by
  intro other owner result returned
  cases found : memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using returned
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, found] using returned
          | suspended =>
              by_cases same : other = handle
              · subst other
                simp [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put] at returned
              · simpa only [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned

/-- Node publication and demand introduce no returned value. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginNode request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  refine ⟨?_, stored.edges⟩
  intro handle owner result returned
  exact stored.nodes handle owner result
    (lookup_returned_before request.key request before.nodeResults handle owner result
      (demand_returned_before published.1 published.2 handle owner result returned))

/-- Edge publication and demand introduce no returned value. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  refine ⟨stored.nodes, ?_⟩
  intro handle owner result returned
  exact stored.edges handle owner result
    (lookup_returned_before request.key request before.edgeResults handle owner result
      (demand_returned_before published.1 published.2 handle owner result returned))

/-- Node completion installs the derived law at the exact evaluating owner. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : NodeCertificate owner result) :
    Stored (SourceCurrentAllocatedPartialState.finishNode handle result before) := by
  refine ⟨?_, stored.edges⟩
  intro other original output returned
  by_cases same : other = handle
  · subst other
    have installed := finishNode_returned handle owner result before running
    have equal := Option.some.inj (installed.symm.trans returned)
    cases equal
    exact law
  · exact stored.nodes other original output (by
      change (FlatMemoThunk.finish handle result before.nodeResults).cells other = _ at returned
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned)

/-- Edge completion installs the derived law at the exact evaluating owner. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : EdgeCertificate owner result) :
    Stored (SourceCurrentAllocatedPartialState.finishEdge handle result before) := by
  refine ⟨stored.nodes, ?_⟩
  intro other original output returned
  by_cases same : other = handle
  · subst other
    have installed := finishEdge_returned handle owner result before running
    have equal := Option.some.inj (installed.symm.trans returned)
    cases equal
    exact law
  · exact stored.edges other original output (by
      change (FlatMemoThunk.finish handle result before.edgeResults).cells other = _ at returned
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned)

/-- Coherent complete node readback transports a warm owner's certificate to its requested value. -/
theorem Stored.node_hit {before : Caller width} (stored : Stored before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    {handle : Nat} {owner request : NodeRequest} {result : Node}
    (returned : before.nodeResults.cells handle = some ⟨owner, .returned result⟩)
    (ownerAvailable : Available before.checked.native.machine.heap owner.value)
    (available : Available before.checked.native.machine.heap request.value)
    (key : owner.key = request.key) : NodeCertificate request result := by
  have same := SourceEqualityPartialKeyTransport.available_reference_eq _ coherent owner.value request.value
    ownerAvailable available (congrArg Prod.snd key)
  simpa only [NodeCertificate, same] using stored.nodes handle owner result returned

/-- Coherent complete edge readback transports the actual warm owner's certificate. -/
theorem Stored.edge_hit {before : Caller width} (stored : Stored before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    {handle : Nat} {owner request : EdgeRequest} {result : Edge}
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩)
    (ownerResident : EdgeResident before.checked.native.machine.heap owner.value)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (key : owner.key = request.key) : EdgeCertificate request result := by
  have same := edge_identity_unique _ coherent owner.value request.value ownerResident resident (congrArg Prod.snd key)
  simpa only [EdgeCertificate, same] using stored.edges handle owner result returned

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned
