import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Current terminal node bodies from initial caller facts

Empty and explicit union bodies return their input. A resident Mu body
rebuilds to cleanup from the initial filtered probes. These branches
retain the whole caller and the original global bundle. Their literal
workers succeed at every bound, including zero. Mu cleanup can remove
the binder. No structural Region of the result is asserted.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeBody)
open SourceCurrentAllocatedPartialSourceReads (NodeBodyReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeBodyTrace)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}

/-- Terminal source bodies stop at Empty, explicit union, or Mu reconstruction. -/
inductive Terminal : Node → Prop where
  | empty : Terminal .empty
  | union : Terminal (.union entry members depth free)
  | binder : Terminal (.mu entry body depth ordinary)

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
    (available : Available before.checked.native.machine.heap request.value) (stored : Stored before)
    (terminal : Terminal request.value) (actual : NodeBody budget request before result before)
    (reads : NodeBodyReads formulas solver actual memos memos) :
    NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Stored before ∧ NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  have checks := terminal_checks terminal actual
  obtain ⟨next, post, resultAvailable, law⟩ :=
    SourceCurrentAllocatedPartialActual.node_body formulas solver reads inventory checks initial inheritedReady available
  exact ⟨reads, checks, Post.refl initial, resultAvailable, stored, law, terminal_done terminal actual⟩

/-- Initial caller facts construct the terminal graph, exact return, and literal zero-bound execution. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (stored : Stored before)
    (terminal : Terminal request.value) :
    ∃ result, ∃ actual : NodeBody budget request before result before,
      NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Stored before ∧ NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  cases request with
  | mk inherited value =>
      cases terminal with
      | empty =>
          exact ⟨.empty, .empty, terminal_receipt formulas solver initial inheritedReady available stored .empty .empty .empty⟩
      | union =>
          exact ⟨_, .union, terminal_receipt formulas solver initial inheritedReady available stored .union .union .union⟩
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
          exact ⟨_, actual, terminal_receipt formulas solver initial inheritedReady available stored .binder actual reads⟩

end MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal
