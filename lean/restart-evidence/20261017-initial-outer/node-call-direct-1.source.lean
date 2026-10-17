import MicroCFTA.SourceCurrentNodeTerminalNumeric
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

/-!
# Initial numeric completion for terminal outer node calls

Ready hits retain the complete caller for every input shape. An evaluated
terminal owner constructs its own body from initial caller facts. Its
checked state and numeric profile stay exact. Busy cells retain their
literal diagnostic. Ordinary recursive node completion remains separate.
-/
namespace MicroCFTA.SourceCurrentNodeCallNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentNodeTerminalNumeric (Terminal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
namespace Graph
export SourceCurrentAllocatedPartialGraph (NodeCall)
export SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
end Graph
variable {width : Nat}

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- One node return retains strict reads, the full caller, and all ten literal fuels. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (request : NodeRequest) (before : Caller width)
    (memos : Memos) (result : Node) (after : Caller width) : Prop where
  /-- The actual source graph retains the selected owner. -/
  actual : Graph.NodeCall budget request before result after
  /-- Strict global reads belong to the same source graph. -/
  reads : Graph.NodeCallReads formulas solver actual memos memos
  /-- Terminal bodies and ready hits require no parent machine checks. -/
  checks : Checks (nodeCallTrace actual)
  /-- The complete caller keeps the original inventory and global bundle. -/
  post : Post formulas solver inventory before after memos
  /-- The actual returned value remains available. -/
  available : Available after.checked.native.machine.heap result
  /-- The candidate retains its inherited-conditioned language law. -/
  law : NodeLaw formulas solver request result
  /-- The full Frame uses the same returned inventory. -/
  frame : Frame formulas solver inventory after.checked
  /-- These branches retain the initial numeric profile. -/
  fits : Fits profile after.checked
  /-- Every fuel is arbitrary, including zero. -/
  run : ∀ f g s r e p h m c n,
    SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before = .done result after

/-- A ready node cell needs no shape restriction, body reservation, or positive fuel. -/
theorem ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    {handle : Nat} {result : Node} {after : Caller width}
    (started : beginNode request before = (handle, .ready result, after)) :
    after = before ∧ Receipt formulas solver inventory profile budget request before memos result after := by
  obtain ⟨same, _, _⟩ := SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request before
    initial.sound initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
    inherited available handle result after started
  obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver initial inherited available started
  subst after
  exact ⟨rfl, .hit started, .hit (started := started), SourceCurrentAllocatedPartialChecksComposition.node_hit started,
    post, output, law, frame, fits,
    fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall_ready
      f g s r e p h m c n budget request before before handle result started⟩

/-- A terminal candidate runs its actual stored owner and publishes that owner's exact result. -/
theorem terminal_evaluated
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (terminal : Terminal request.value)
    {handle : Nat} {original : NodeRequest} {running : Caller width}
    (started : beginNode request before = (handle, .evaluate original, running)) :
    ∃ result, Receipt formulas solver inventory profile budget request before memos result (finishNode handle result running) ∧
      (finishNode handle result running).nodeResults.cells handle = some ⟨original, .returned result⟩ := by
  obtain ⟨runningContext, owner, key, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
  have components := beginNode_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, _merge, _fourth, _edges⟩ := components
  have same := SourceEqualityPartialKeyTransport.available_reference_eq running.checked.native.machine.heap
    runningContext.ready.semantic.ready.semantic.1.normal.facts.coherent original.value request.value owner.input
    (by simpa only [checked] using available) (congrArg Prod.snd key)
  have ownerTerminal : Terminal original.value := by simpa only [same] using terminal
  have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
  have runningFits : Fits profile running.checked := by simpa only [checked] using fits
  obtain ⟨result, body⟩ := SourceCurrentNodeTerminalNumeric.complete formulas solver inventory budget original running memos
    runningContext runningFrame profile runningFits owner.inherited owner.input ownerTerminal
  obtain ⟨post, output, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver initial inherited available
    started body.actual body.post body.available body.law
  refine ⟨result, ⟨.evaluate started body.actual, .evaluate (started := started) body.reads,
    SourceCurrentAllocatedPartialChecksComposition.node_evaluate started body.actual body.checks,
    post, output, law, body.frame, body.fits, ?_⟩,
    finishNode_returned handle original result running cell⟩
  intro f g s r e p h m c n
  exact SourceCurrentAllocatedPartialWorker.nodeCall_body_done f g s r e p h m c n budget request original
    before running running handle result started (body.run f g s r e p h m c n)

end

private theorem not_absent (request : NodeRequest) (before : Caller width)
    (valid : SourceCurrentAllocatedPartialState.Valid before)
    (inherited : EqReady before.checked.operations.constraints request.inherited) :
    (beginNode request before).2.1 ≠ .absent := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have next := FlatMemoThunk.lookup_valid request.key request before.nodeResults
    (NodeLinked before.checked.operations.constraints) (fun _ => True) valid.nodes ⟨inherited.1, rfl⟩ trivial
  obtain ⟨cell, found, _⟩ := next.linked request.key published.1 (FlatMemoThunk.lookup_stored _ _ _)
  change published.2.cells published.1 = some cell at found
  change (FlatMemoThunk.demand published.1 published.2).1 ≠ .absent
  cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase] <;> simp

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A terminal input either retains its exact busy fault or constructs its own full node return. -/
theorem finite_or_busy_terminal
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (terminal : Terminal request.value) :
    (∃ handle running, beginNode request before = (handle, .busy, running) ∧
      ∀ f g s r e p h m c n, SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before =
        .failed (.nodeMemo handle .busy) running) ∨
      ∃ result after, Receipt formulas solver inventory profile budget request before memos result after := by
  generalize started : beginNode request before = observed
  obtain ⟨handle, observation, running⟩ := observed
  cases observation with
  | ready result =>
      exact Or.inr ⟨result, running,
        (ready formulas solver inventory budget request before memos initial frame profile fits inherited available started).2⟩
  | evaluate original =>
      obtain ⟨result, receipt, _⟩ := terminal_evaluated formulas solver inventory budget request before memos
        initial frame profile fits inherited available terminal started
      exact Or.inr ⟨result, _, receipt⟩
  | busy =>
      exact Or.inl ⟨handle, running, started,
        fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall_busy
          f g s r e p h m c n budget request before running handle started⟩
  | absent =>
      exact False.elim (not_absent request before initial.sound.valid inherited (by rw [started]))

/-- Excluding only this queried busy cell completes terminal node calls from initial facts. -/
theorem terminal_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (terminal : Terminal request.value)
    (notBusy : (beginNode request before).2.1 ≠ .busy) :
    ∃ result after, Receipt formulas solver inventory profile budget request before memos result after := by
  rcases finite_or_busy_terminal formulas solver inventory budget request before memos
      initial frame profile fits inherited available terminal with busy | completed
  · obtain ⟨handle, running, started, _⟩ := busy
    exact False.elim (notBusy (by rw [started]))
  · exact completed

end
end MicroCFTA.SourceCurrentNodeCallNumeric
