import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState

/-!
# Produced quantitative certificates for actual outer edge calls

The edge body verifies its same literal parent reads at every input envelope.
It derives the universal owner law before the actual finish operation.
A warm hit reads the certificate for its complete captured owner.
Outer node certificates stay unchanged because the body has no outer node call.
No future profile, constructor headroom, or body-law premise is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The supplied parent reads produce the universal edge law and preserve complete outer stores. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow request.value result ∧ EdgeCertificate request result := by
  have base := SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.edge_body formulas solver reads inventory
    initial inherited resident domain stored.base
  cases reads with
  | parent parentReads =>
      rename_i edge loaded originalInherited checked fourth merge field parent
      have live : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
          SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
          SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
          EqReady before.checked.operations.constraints originalInherited ∧
          InternedNestedProvenance.Values before.checked.native.machine.heap edge.children := by
        intro test
        exact ⟨(initial.ready.good.fields edge.entry.key edge resident).1, field test, inherited,
          initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ edge resident⟩
      refine ⟨⟨base.1, stored.returned.advance checked fourth merge⟩, base.2, ?_⟩
      intro rows arity bound limits shape profile bounded
      have produced := SourceCurrentAllocatedFiniteOrdinaryParentShapes.structure_from_reads formulas solver inventory edge
        parentReads initial.ready initial.admitted live limits profile initial.correct initial.stored initial.covered
        stored.base.native stored.base.profiles stored.base.output initial.globals stored.base.nativeGuard stored.base.mergeGuard
        rows arity bound shape bounded
      exact ⟨produced.2.2.2.2.2.1, produced.2.2.2.2.2.2.1⟩

/-- Literal evaluation installs its derived owner law; ready calls read that exact stored law. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow request.value result ∧ EdgeCertificate request result := by
  cases reads with
  | hit =>
      rename_i handle started
      have quantitative := stored.edge_ready formulas solver request after handle result initial.sound
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident started
      have narrowed := stored.structural.edge_ready formulas solver request after handle result initial.sound
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident domain started
      exact ⟨quantitative.1.symm ▸ stored, narrowed.2, quantitative.2⟩
  | evaluate bodyReads =>
      rename_i original running middle handle started body
      obtain ⟨runningContext, owner, key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
        initial inherited resident started
      obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver request original
        before running handle initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
      have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
      have produced := edge_body formulas solver bodyReads inventory runningContext owner.inherited owner.input ownerDomain runningStored
      have frame := SourceCurrentAllocatedPartialFrames.edge_body body
        (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
      refine ⟨produced.1.finishEdge result (frame.edge_running handle original cell) (fun _ => produced.2.1) produced.2.2, ?_, ?_⟩
      · simpa only [same] using produced.2.1
      · simpa only [EdgeCertificate, same] using produced.2.2

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes
