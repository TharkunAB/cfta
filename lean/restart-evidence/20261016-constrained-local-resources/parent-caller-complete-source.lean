import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Parent resources with the full returned outer caller

The initial loaded field selects the numeric budget.
The constructed parent graph supplies the same caller body and strict Reads.
Its receipt retains outer cells, probes, global memos, and the language law.
No future range or capacity plan is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCallerResources
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

/-- Initial caller facts and total parent headroom construct the same complete edge body. -/
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
      checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound := by
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  obtain ⟨result, checked, saved, next, final, requests, parent, reads, receipt, stable, finalNative, finalOutput,
    finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.complete formulas solver inventory bits budget request.value loaded
      request.inherited before.checked before.fourth before.merge initial.ready initial.admitted cached found inherited available
      initial.correct initial.stored profiles native output initial.covered memos initial.globals rows arity count depth bound
      profile lengthBound pathsBound heightBound nodes edges
  have ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded request.inherited request.value.children before.checked before.fourth := by
    intro records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) request.value.children
      (records.map SourceEqualityClassOrder.Record.paths) (prefixState before.checked loaded request.inherited) before.fourth
      initial.ready.good.native.machine.1.coherent available (ChildrenShape.domain request.value.children profile)
  have probes := SourceCurrentAllocatedProbeParent.parent_heap formulas solver inventory reads initial.ready initial.admitted
    (fun _ => ⟨cached, found, inherited, available, ranges⟩) initial.correct initial.stored initial.covered initial.globals initial.probes
  have sound := initial.sound.advance formulas solver checked before.fourth saved receipt.effects
  have post : Post formulas solver next before (advance before checked before.fourth saved) final :=
    ⟨⟨receipt.ready, receipt.admitted, sound, receipt.stored, receipt.covered, receipt.correct, receipt.globals, probes⟩,
      receipt.effects, receipt.retained, receipt.fourthRetained⟩
  have law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
    intro ambient term
    have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term
    change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term ↔
      SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        request.value.entry.key.symbol request.value.entry.key.constraint request.value.children term at input
    exact ⟨fun accepted => input.mpr ((receipt.language ambient term).1 accepted),
      fun satisfied => ((receipt.language ambient term).2 satisfied).trans input.symm⟩
  let actual : EdgeBody budget request before result (advance before checked before.fourth saved) :=
    .parent (fun _ => found) parent
  have bodyReads : EdgeBodyReads formulas solver actual memos final := .parent (field := fun _ => found) reads
  exact ⟨result, checked, saved, next, final, requests, actual, bodyReads,
    ⟨receipt.ready, receipt.admitted, sound, receipt.effects, receipt.resident, receipt.stored, receipt.covered,
      receipt.retained, receipt.globals, receipt.correct, receipt.fourthRetained, rfl, law⟩,
    post, stable, finalNative, finalOutput, finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCallerResources
