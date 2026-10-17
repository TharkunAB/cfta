import MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame

/-!
# Initial numeric completion of terminal outer node bodies

Empty and explicit union bodies return their input. A resident Mu body
rebuilds to cleanup from the initial filtered probes. These branches
retain the whole caller and the original global bundle. Their literal
workers succeed at every bound, including zero. Mu cleanup can remove
the binder. The initial Frame and Fits remain exact. No finite Cap,
returned-domain store, input closure, or future completed worker is required.
-/
namespace MicroCFTA.SourceCurrentNodeTerminalNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeBody)
open SourceCurrentAllocatedPartialSourceReads (NodeBodyReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeBodyTrace)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}

export SourceCurrentAllocatedPartialPlainTerminal (Terminal)

private theorem terminal_checks {request : NodeRequest} {before after : Caller width} {result : Node}
    (terminal : Terminal request.value) (actual : NodeBody budget request before result after) :
    Checks (nodeBodyTrace actual) := by
  cases actual <;> cases terminal
  all_goals
    intro edgeRequest edgeBefore edgeResult edgeAfter edgeActual reached
    cases reached with
    | step first rest => cases first

private theorem terminal_done {request : NodeRequest} {before after : Caller width} {result : Node}
    (terminal : Terminal request.value) (actual : NodeBody budget request before result after)
    (f g s r e p h m c n : Nat) :
    SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result after := by
  cases actual <;> cases terminal
  all_goals simp_all only [SourceCurrentAllocatedPartialWorker.nodeBody]

private theorem terminal_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : NodeRequest} {before : Caller width} {memos : Memos} {result : Node}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (terminal : Terminal request.value) (actual : NodeBody budget request before result before)
    (reads : NodeBodyReads formulas solver actual memos memos) :
    NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Frame formulas solver inventory before.checked ∧ Fits profile before.checked ∧
      NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  have checks := terminal_checks terminal actual
  obtain ⟨next, post, resultAvailable, law⟩ :=
    SourceCurrentAllocatedPartialActual.node_body formulas solver reads inventory checks initial inheritedReady available
  exact ⟨reads, checks, Post.refl initial, resultAvailable, frame, fits, law, terminal_done terminal actual⟩

/-- Initial caller facts construct the terminal graph, exact return, and literal zero-bound execution. -/
private theorem complete_raw
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (terminal : Terminal request.value) :
    ∃ result, ∃ actual : NodeBody budget request before result before,
      NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Frame formulas solver inventory before.checked ∧ Fits profile before.checked ∧
      NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  cases request with
  | mk inherited value =>
      cases terminal with
      | empty =>
          exact ⟨.empty, .empty, terminal_receipt formulas solver initial inheritedReady available frame profile fits .empty .empty .empty⟩
      | union =>
          exact ⟨_, .union, terminal_receipt formulas solver initial inheritedReady available frame profile fits .union .union .union⟩
      | @binder entry body depth ordinary =>
          have rebuilt := SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked initial.ready initial.probes
            entry body depth ordinary available
          have unchanged : SourceCurrentAllocatedPartialState.advance before
              (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                ⟨before.checked.native.machine.heap, before.checked.operations⟩) before.fourth before.merge = before := by
            cases before
            rfl
          have actual : NodeBody budget ⟨inherited, .mu entry body depth ordinary⟩ before
              (cleanup (.mu entry body depth ordinary)) before := by
            simpa only [unchanged] using
              (NodeBody.binder (budget := budget) (inherited := inherited) rebuilt.1)
          have reads : NodeBodyReads formulas solver actual memos memos := by
            have rawReads : NodeBodyReads formulas solver
                (NodeBody.binder (budget := budget) (inherited := inherited) rebuilt.1) memos memos := .binder (actual := rebuilt.1)
            simpa only [unchanged] using rawReads
          exact ⟨_, actual, terminal_receipt formulas solver initial inheritedReady available frame profile fits .binder actual reads⟩

/-- A terminal body retains the exact caller, inventory, profile, and global memo bundle. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (result : Node) : Prop where
  /-- The actual terminal graph returns at the unchanged complete caller. -/
  actual : NodeBody budget request before result before
  /-- Strict source reads retain the original global memo bundle. -/
  reads : NodeBodyReads formulas solver actual memos memos
  /-- A terminal body contains no descendant edge checks. -/
  checks : Checks (nodeBodyTrace actual)
  /-- The original caller keeps all current laws and completed histories. -/
  post : Post formulas solver inventory before before memos
  /-- The returned cleanup or stopped value is available in the original heap. -/
  available : Available before.checked.native.machine.heap result
  /-- The query Frame retains the same inventory and complete checked state. -/
  frame : Frame formulas solver inventory before.checked
  /-- The initial numeric profile remains exact. -/
  fits : Fits profile before.checked
  /-- The result has the existing guarded outer node language law. -/
  law : NodeLaw formulas solver request result
  /-- All ten worker fuels are arbitrary, including zero. -/
  run : ∀ f g s r e p h m c n,
    SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before

/-- Initial facts construct every terminal body without a future worker or input shape bound. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : NodeRequest) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (terminal : Terminal request.value) :
    ∃ result, Receipt formulas solver inventory profile budget request before memos result := by
  obtain ⟨result, actual, reads, checks, post, output, returned, numeric, law, done⟩ :=
    complete_raw formulas solver budget request initial inheritedReady available frame profile fits terminal
  exact ⟨result, actual, reads, checks, post, output, returned, numeric, law, done⟩

end MicroCFTA.SourceCurrentNodeTerminalNumeric
