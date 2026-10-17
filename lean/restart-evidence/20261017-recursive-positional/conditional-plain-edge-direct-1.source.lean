import MicroCFTA.SourceCurrentAllocatedParentPlain
import MicroCFTA.SourceCurrentAllocatedPartialConditionalFrames
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

/-!
# Constructed plain edge calls in mixed outer caches

The filtered active bound excludes busy and absent demand for a plain
request. Other active and returned constrained owners remain unrestricted.
The actual parent producer derives the result shape before exact finish.
A warm hit uses the actual stored owner's conditional certificate.
No future execution, range plan, or desired result is an input premise.
Mixed outer node and descendant completion remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainEdge
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove PlainEdge)
open SourceCurrentAllocatedPartialActiveOrder (edgeRank)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem evaluate
    {inventory : Inventory} {budget handle : Nat} {request owner : EdgeRequest}
    {before running : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : PlainEdge request.value) (stored : Stored before)
    (started : beginEdge request before = (handle, .evaluate owner, running)) :
    ∃ result after next final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ Shape request.value result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨current, good, key, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  have same : owner.value = request.value := edge_identity_unique before.checked.native.machine.heap
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent _ _
    (by simpa only [components.1] using good.input) resident (congrArg Prod.snd key)
  have ownerPlain : SourceCurrentAllocatedParentPlain.Plain owner := by
    intro _
    simpa only [same] using plain.1
  obtain ⟨result, checked, fourth, memo, next, final, _stable, body, reads, receipt, post, shape, _height⟩ :=
    SourceCurrentAllocatedParentPlain.finite formulas solver budget owner current good.inherited good.input ownerPlain
  let middle := SourceCurrentAllocatedPartialState.advance running checked fourth memo
  let actual : EdgeCall budget request before result (finishEdge handle result middle) := .evaluate started body
  have bodyChecks := SourceCurrentAllocatedPartialChecksComposition.edge_body body
    (SourceCurrentAllocatedPartialChecksComposition.resident_ranges
      (SourceCurrentAllocatedParentPlain.resident_ranges formulas solver budget owner current good.inherited good.input ownerPlain))
  obtain ⟨finished, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish formulas solver
    initial inherited resident started body post receipt.resident receipt.language
  have runningStored : Stored running := by
    simpa only [started] using stored.beginEdge request
  have middleStored : Stored middle := runningStored.advance checked fourth memo
  have storedResult := middleStored.finishEdge result cell (fun _ => shape)
  exact ⟨result, finishEdge handle result middle, next, final, actual,
    .evaluate (started := started) reads, SourceCurrentAllocatedPartialChecksComposition.edge_evaluate started body bodyChecks,
    finished, available, storedResult, by simpa only [same] using shape, law⟩

/-- A plain request constructs its finite return among arbitrary mixed outer owners. -/
theorem finite
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : PlainEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ Shape request.value result ∧ EdgeLaw formulas solver request result := by
  have safe := SourceCurrentAllocatedPartialConditionalActive.edge_begin_safe formulas solver request before
    initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident plain active
  rcases safe with ⟨result, ready⟩ | ⟨owner, start⟩
  · have started : beginEdge request before =
        ((beginEdge request before).1, .ready result, (beginEdge request before).2.2) :=
      Prod.ext rfl (Prod.ext ready rfl)
    obtain ⟨same, shape⟩ := SourceCurrentAllocatedPartialConditionalDomain.edge_ready_shape
      formulas solver request before (beginEdge request before).2.2 (beginEdge request before).1 result
      initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident plain.1 stored started
    obtain ⟨post, available, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver
      initial inherited resident started
    let actual : EdgeCall budget request before result (beginEdge request before).2.2 := .hit started
    refine ⟨result, (beginEdge request before).2.2, inventory, memos,
      SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete actual, actual,
      .hit (started := started), SourceCurrentAllocatedPartialChecksComposition.edge_hit started, post, available, ?_, shape, law⟩
    simpa only [same] using stored
  · have started : beginEdge request before =
        ((beginEdge request before).1, .evaluate owner, (beginEdge request before).2.2) :=
      Prod.ext rfl (Prod.ext start rfl)
    obtain ⟨result, after, next, final, actual, reads, checks, post, available, retained, shape, law⟩ :=
      evaluate formulas solver initial inherited resident plain stored started
    exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.edgeCall_complete actual,
      actual, reads, checks, post, available, retained, shape, law⟩

end MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainEdge
