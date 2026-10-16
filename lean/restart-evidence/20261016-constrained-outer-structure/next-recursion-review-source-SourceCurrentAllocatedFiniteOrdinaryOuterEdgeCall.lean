import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition
import MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion

/-!
# Constructed constrained finite ordinary outer edge calls

A ready observation uses its actual captured owner's certificate.
An evaluating observation constructs the current parent producer.
Rejection needs no field load or child range plan. A live evaluation uses
only the ranges at its actual captured owner and current checked state.
The exact finish publishes the derived bound at the same running handle.
The full guard, warm tables, strict reads, and computed inventory remain.
This result does not construct outer node or descendant recursion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall
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
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Only an actual evaluating owner selects the live parent range plan. -/
def Ranges (budget : Nat) (request : EdgeRequest) (before : Caller width) : Prop :=
  ∀ handle owner running, beginEdge request before = (handle, .evaluate owner, running) →
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner running

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem parent
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before) :
    ∃ result checked fourth memo next final,
      ∃ actual : EdgeBody budget request before result (advance before checked fourth memo),
        EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual) ∧
        Post formulas solver next before (advance before checked fourth memo) final ∧
        EdgeResident checked.native.machine.heap result ∧ NativeStored checked.native ∧ MergeStored memo ∧
        EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  have construct : ∃ (loaded : Allocated), ∃ result checked fourth memo,
      ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children before.checked
        before.fourth before.merge result checked fourth memo,
      ∃ final, SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final ∧
        (contradictory request.value.entry.key.constraint = false →
          SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
            .ok (some loaded)) ∧
        NativeStored checked.native ∧ MergeStored memo ∧ EdgeNarrow request.value result := by
    cases test : contradictory request.value.entry.key.constraint with
    | true =>
        let loaded : Allocated := ⟨.contradiction, request.value.entry.key.constraint.guard⟩
        obtain ⟨_stable, actual, reads, _receipt, native, merged, narrow⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryParent.rejected_finite formulas solver inventory budget request.value
            loaded request.inherited before.checked before.fourth before.merge initial.ready initial.admitted test
            initial.correct initial.stored initial.covered stored.native stored.merge memos initial.globals
        refine ⟨loaded, _, _, before.fourth, before.merge, actual, memos, reads, ?_, native, merged, narrow⟩
        intro impossible
        cases impossible
    | false =>
        obtain ⟨cached, loaded, found⟩ := initial.ready.good.fields request.value.entry.key request.value resident
        have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
        obtain ⟨result, checked, fourth, memo, _next, final, _stable, actual, reads, _receipt, native, merged, narrow⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryParent.finite formulas solver inventory budget request.value loaded
            request.inherited before.checked before.fourth before.merge initial.ready initial.admitted cached found
            inherited available domain initial.correct initial.stored initial.covered
            (fun _ => ranges test loaded found) stored.native stored.merge memos initial.globals
        exact ⟨loaded, result, checked, fourth, memo, actual, final, reads, fun _ => found, native, merged, narrow⟩
  obtain ⟨loaded, result, checked, fourth, memo, parent, final, reads, field, native, merged, narrow⟩ := construct
  let actual : EdgeBody budget request before result (advance before checked fourth memo) := .parent field parent
  have actualReads : EdgeBodyReads formulas solver actual memos final := .parent (field := field) reads
  have checks := SourceCurrentAllocatedPartialChecksComposition.edge_body actual
    (SourceCurrentAllocatedPartialChecksComposition.resident_ranges ranges)
  obtain ⟨next, post, available, law⟩ := SourceCurrentAllocatedPartialActual.edge_body formulas solver actualReads
    inventory checks initial inherited resident
  exact ⟨result, checked, fourth, memo, next, final, actual, actualReads, checks, post, available, native, merged, narrow, law⟩

private theorem evaluate
    {inventory : Inventory} {budget handle : Nat} {request owner : EdgeRequest}
    {before running : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner running) :
    ∃ result after next final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨current, good, _key, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate
    formulas solver request owner before running handle initial.sound
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
  have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
  obtain ⟨result, checked, fourth, memo, next, final, body, reads, checks, post, available, native, merged, narrow, law⟩ :=
    parent formulas solver budget owner current good.inherited good.input ownerDomain runningStored ranges
  let middle := advance running checked fourth memo
  let actual : EdgeCall budget request before result (finishEdge handle result middle) := .evaluate started body
  obtain ⟨finished, residentAfter, candidateLaw⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish formulas solver
    initial inherited resident started body post available law
  have middleStored : Stored middle := runningStored.advance checked fourth memo native merged
  have storedResult := middleStored.finishEdge result cell (fun _ => narrow)
  exact ⟨result, finishEdge handle result middle, next, final, actual, .evaluate (started := started) reads,
    SourceCurrentAllocatedPartialChecksComposition.edge_evaluate started body checks,
    finished, residentAfter, storedResult, by simpa only [same] using narrow, candidateLaw⟩

/-- Initial causal certificates and reached live checks construct the same full finite outer return. -/
theorem finite
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) (ranges : Ranges budget request before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  have safe := SourceCurrentAllocatedPartialActiveOrder.edge_begin_safe formulas solver request before
    initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident active
  rcases safe with ⟨result, ready⟩ | ⟨owner, start⟩
  · have started : beginEdge request before =
        ((beginEdge request before).1, .ready result, (beginEdge request before).2.2) := Prod.ext rfl (Prod.ext ready rfl)
    obtain ⟨same, narrow⟩ := stored.edge_ready formulas solver request (beginEdge request before).2.2
      (beginEdge request before).1 result initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent
      resident domain started
    obtain ⟨post, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver
      initial inherited resident started
    let actual : EdgeCall budget request before result (beginEdge request before).2.2 := .hit started
    refine ⟨result, (beginEdge request before).2.2, inventory, memos,
      SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete actual, actual, .hit (started := started),
      SourceCurrentAllocatedPartialChecksComposition.edge_hit started, post, available, ?_, narrow, law⟩
    simpa only [same] using stored
  · have started : beginEdge request before =
        ((beginEdge request before).1, .evaluate owner, (beginEdge request before).2.2) := Prod.ext rfl (Prod.ext start rfl)
    obtain ⟨result, after, next, final, actual, reads, checks, post, available, retained, narrow, law⟩ :=
      evaluate formulas solver initial inherited resident domain stored started (ranges _ _ _ started)
    exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete actual,
      actual, reads, checks, post, available, retained, narrow, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall
