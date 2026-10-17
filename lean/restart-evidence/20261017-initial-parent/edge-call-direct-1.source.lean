import MicroCFTA.SourceCurrentEdgeBodyNumeric
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

/-!
# Initial numeric completion for outer edge result cells

The initial demand selects the stored owner before its body runs.
Only that evaluation branch reserves parent work. Ready hits retain the
complete caller. Busy cells keep their exact diagnostic and require no Room.
The body does not consume the outer recursion fuel.
-/
namespace MicroCFTA.SourceCurrentEdgeCallNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
namespace Graph
export SourceCurrentAllocatedPartialGraph (EdgeCall)
export SourceCurrentAllocatedPartialSourceReads (EdgeCallReads)
end Graph
variable {width bits : Nat}

/-- Only an actual initial evaluation advances the parent profile. -/
noncomputable def finalProfile (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (profile : Profile) : Profile :=
  match (beginEdge request before).2.1 with
  | .evaluate original => SourceCurrentParentForecast.residentProfile budget original
      (beginEdge request before).2.2.checked profile
  | _ => profile

/-- A ready or busy observation does not execute a parent instruction. -/
noncomputable def fuel (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (profile : Profile) : Nat :=
  match (beginEdge request before).2.1 with
  | .evaluate original => SourceCurrentParentForecast.residentFuel budget original
      (beginEdge request before).2.2.checked profile
  | _ => 0

/-- Reservation inspects only the initial stored owner and post-demand state. -/
noncomputable def Reserved (bits budget : Nat) (request : EdgeRequest) (before : Caller width)
    (profile : Profile) : Prop :=
  match (beginEdge request before).2.1 with
  | .evaluate original => SourceCurrentParentForecast.residentReserved bits budget original
      (beginEdge request before).2.2.checked profile
  | _ => True

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- One actual returned edge retains its old law, current inventory, and full caller. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (memos : Memos) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  /-- The actual first-writer graph retains its selected owner. -/
  actual : Graph.EdgeCall budget request before result after
  /-- Strict reads use the same actual graph and global bundle. -/
  reads : Graph.EdgeCallReads formulas solver actual memos final
  /-- The old complete receipt retains the candidate's inherited-conditioned law. -/
  semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before result after final
  /-- The query Frame uses the same returned inventory. -/
  frame : Frame formulas solver inventory after.checked
  /-- The initial branch forecast bounds the actual returned state. -/
  fits : Fits (finalProfile budget request before profile) after.checked
  /-- The full caller postcondition retains all physical memo families. -/
  post : Post formulas solver inventory before after final
  /-- Outer fuel is arbitrary and every lower fuel can increase independently. -/
  run : ∀ f g s r e p h m c n,
    fuel budget request before profile ≤ g → fuel budget request before profile ≤ s →
    fuel budget request before profile ≤ r → fuel budget request before profile ≤ e →
    fuel budget request before profile ≤ p → fuel budget request before profile ≤ h →
    fuel budget request before profile ≤ m → fuel budget request before profile ≤ c →
    fuel budget request before profile ≤ n →
    SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before = .done result after

/-- A ready cell retains the whole caller without a parent resource reservation. -/
theorem ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    {handle : Nat} {result : Edge} {after : Caller width}
    (started : beginEdge request before = (handle, .ready result, after)) :
    after = before ∧ Receipt formulas solver inventory profile budget request before memos result after memos := by
  obtain ⟨same, _actual, _reads, semantic⟩ := SourceCurrentAllocatedPartialEdgeCall.ready_hit
    formulas solver inventory budget request before initial.ready initial.admitted initial.sound inherited resident
    initial.correct initial.stored initial.covered handle result after started memos initial.globals
  obtain ⟨post, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver initial inherited resident started
  subst after
  exact ⟨rfl, .hit started, .hit (started := started), semantic, frame,
    by simpa only [finalProfile, started] using fits, post,
    fun f g s r e p h m c n _ _ _ _ _ _ _ _ _ =>
      SourceCurrentAllocatedPartialWorker.edgeCall_ready f g s r e p h m c n budget request before before handle result started⟩

/-- An initial evaluated owner runs its own parent and finishes its exact protected cell. -/
theorem evaluated
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : Reserved bits budget request before profile)
    {handle : Nat} {original : EdgeRequest} {running : Caller (bits + 2)}
    (started : beginEdge request before = (handle, .evaluate original, running)) :
    ∃ result after next final,
      Receipt formulas solver next profile budget request before memos result after final ∧
      after.edgeResults.cells handle = some ⟨original, .returned result⟩ := by
  obtain ⟨runningContext, owner, _, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, _merge, _fourth, nodes⟩ := components
  have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
  have runningFits : Fits profile running.checked := by simpa only [checked] using fits
  have room : SourceCurrentParentForecast.residentReserved bits budget original running.checked profile := by
    simpa only [Reserved, started] using reserved
  obtain ⟨result, middle, next, final, body⟩ :=
    SourceCurrentEdgeBodyNumeric.complete formulas solver inventory budget original running memos
      runningContext runningFrame profile runningFits (fun _ => owner.input) (fun _ => owner.inherited) room
  obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish formulas solver initial
    inherited resident started body.actual body.post body.semantic.resident body.semantic.language
  have protected := SourceCurrentAllocatedPartialFrames.edge_body body.actual
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have current := protected.edge_running handle original cell
  have semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
      (finishEdge handle result middle) final :=
    ⟨post.context.ready, post.context.admitted, post.context.sound, post.effects, output,
      post.context.stored, post.context.covered, post.retained, post.context.globals, post.context.correct,
      post.fourthRetained, body.semantic.nodes.trans nodes, law⟩
  refine ⟨result, finishEdge handle result middle, next, final,
    ⟨.evaluate started body.actual, .evaluate (started := started) body.reads, semantic, body.frame,
      ?_, post, ?_⟩, finishEdge_returned handle original result middle current⟩
  · simpa only [finalProfile, started, finishEdge] using body.fits
  · intro f g s r e p h m c n hg hs hr he hp hh hm hc hn
    have done := body.run f g s r e p h m c n
      (by simpa only [fuel, started] using hg) (by simpa only [fuel, started] using hs)
      (by simpa only [fuel, started] using hr) (by simpa only [fuel, started] using he)
      (by simpa only [fuel, started] using hp) (by simpa only [fuel, started] using hh)
      (by simpa only [fuel, started] using hm) (by simpa only [fuel, started] using hc)
      (by simpa only [fuel, started] using hn)
    exact SourceCurrentAllocatedPartialWorker.edgeCall_body_done f g s r e p h m c n budget request original
      before running middle handle result started done

end

private theorem not_absent (request : EdgeRequest) (before : Caller width)
    (valid : SourceCurrentAllocatedPartialState.Valid before)
    (inherited : EqReady before.checked.operations.constraints request.inherited) :
    (beginEdge request before).2.1 ≠ .absent := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have next := FlatMemoThunk.lookup_valid request.key request before.edgeResults
    (EdgeLinked before.checked.operations.constraints) (fun _ => True) valid.edges ⟨inherited.1, rfl⟩ trivial
  obtain ⟨cell, found, _⟩ := next.linked request.key published.1 (FlatMemoThunk.lookup_stored _ _ _)
  change published.2.cells published.1 = some cell at found
  change (FlatMemoThunk.demand published.1 published.2).1 ≠ .absent
  cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase] <;> simp

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Valid warm tables either retain an exact busy diagnostic or construct a complete edge call. -/
theorem finite_or_busy
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : Reserved bits budget request before profile) :
    (∃ handle running, beginEdge request before = (handle, .busy, running) ∧
      ∀ f g s r e p h m c n, SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before =
        .failed (.edgeMemo handle .busy) running) ∨
      ∃ result after next final, Receipt formulas solver next profile budget request before memos result after final := by
  generalize started : beginEdge request before = observed
  obtain ⟨handle, observation, running⟩ := observed
  cases observation with
  | ready result =>
      exact Or.inr ⟨result, running, inventory, memos,
        (ready formulas solver inventory budget request before memos initial frame profile fits inherited resident started).2⟩
  | evaluate original =>
      obtain ⟨result, after, next, final, receipt, _⟩ := evaluated formulas solver inventory budget request before memos
        initial frame profile fits inherited resident reserved started
      exact Or.inr ⟨result, after, next, final, receipt⟩
  | busy =>
      exact Or.inl ⟨handle, running, started,
        fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall_busy
          f g s r e p h m c n budget request before running handle started⟩
  | absent =>
      exact False.elim (not_absent request before initial.sound.valid inherited (by rw [started]))

/-- Excluding only the queried initial busy observation constructs the complete numeric call. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : Reserved bits budget request before profile)
    (notBusy : (beginEdge request before).2.1 ≠ .busy) :
    ∃ result after next final, Receipt formulas solver next profile budget request before memos result after final := by
  rcases finite_or_busy formulas solver inventory budget request before memos initial frame profile fits
      inherited resident reserved with busy | completed
  · obtain ⟨handle, running, started, _⟩ := busy
    exact False.elim (notBusy (by rw [started]))
  · exact completed

end
end MicroCFTA.SourceCurrentEdgeCallNumeric
