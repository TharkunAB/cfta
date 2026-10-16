import MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.empty
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.empty
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.union
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.union
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.binder
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.Terminal.binder
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.complete
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal.complete

namespace TerminalChecks
open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState (NodeRequest beginNode finishNode)
open SourceCurrentAllocatedPartialGraph (NodeBody NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeBodyReads NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialPlainTerminal
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "nodeBody" => SourceCurrentAllocatedPartialWorker.nodeBody
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

theorem empty_zero
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos} (budget : Nat)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited) (stored : Stored before) :
    nodeBody 0 0 0 0 0 0 0 0 0 0 budget ⟨inherited, .empty⟩ before = .done .empty before ∧
      Post formulas solver inventory before before memos ∧ Stored before := by
  obtain ⟨result, actual, reads, checks, post, available, retained, law, done⟩ :=
    complete formulas solver budget ⟨inherited, .empty⟩ initial ready (empty_available _) stored .empty
  have zero := done 0 0 0 0 0 0 0 0 0 0
  simp only [SourceCurrentAllocatedPartialWorker.nodeBody] at zero
  cases zero
  exact ⟨by simp only [SourceCurrentAllocatedPartialWorker.nodeBody], post, retained⟩

theorem union_members_opaque
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos} (budget : Nat)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (entry : Interned InternedBinderProtocol.NodeKey) (members : List Node) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (available : Available before.checked.native.machine.heap (.union entry members depth free)) (stored : Stored before) :
    ∃ actual : NodeBody budget ⟨inherited, .union entry members depth free⟩ before (.union entry members depth free) before,
      NodeBodyReads formulas solver actual memos memos ∧
      NodeLaw formulas solver ⟨inherited, .union entry members depth free⟩ (.union entry members depth free) ∧
      nodeBody 0 0 0 0 0 0 0 0 0 0 budget ⟨inherited, .union entry members depth free⟩ before =
        .done (.union entry members depth free) before := by
  obtain ⟨result, actual, reads, checks, post, resident, retained, law, done⟩ :=
    complete formulas solver budget ⟨inherited, .union entry members depth free⟩ initial ready available stored .union
  have zero := done 0 0 0 0 0 0 0 0 0 0
  simp only [SourceCurrentAllocatedPartialWorker.nodeBody] at zero
  cases zero
  exact ⟨actual, reads, law, by simp only [SourceCurrentAllocatedPartialWorker.nodeBody]⟩

theorem mu_cleanup
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos} (budget : Nat)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Node)
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (available : Available before.checked.native.machine.heap (.mu entry body depth ordinary)) (stored : Stored before) :
    ∃ actual : NodeBody budget ⟨inherited, .mu entry body depth ordinary⟩ before
        (cleanup (.mu entry body depth ordinary)) before,
      NodeBodyReads formulas solver actual memos memos ∧
      NodeLaw formulas solver ⟨inherited, .mu entry body depth ordinary⟩ (cleanup (.mu entry body depth ordinary)) ∧
      (cleanup (.mu entry body depth ordinary)).free = (Value.mu entry body depth ordinary).free ∧
      nodeBody 0 0 0 0 0 0 0 0 0 0 budget ⟨inherited, .mu entry body depth ordinary⟩ before =
        .done (cleanup (.mu entry body depth ordinary)) before := by
  have clean := SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked initial.ready initial.probes
    entry body depth ordinary available
  obtain ⟨result, actual, reads, checks, post, resident, retained, law, done⟩ :=
    complete formulas solver budget ⟨inherited, .mu entry body depth ordinary⟩ initial ready available stored .binder
  have zero := done 0 0 0 0 0 0 0 0 0 0
  have same : cleanup (.mu entry body depth ordinary) = result := by
    simp only [SourceCurrentAllocatedPartialWorker.nodeBody, clean.1] at zero
    exact (SourceCurrentAllocatedPartialWorker.Outcome.done.inj zero).1
  cases same
  exact ⟨actual, reads, law, clean.2.2.1, done 0 0 0 0 0 0 0 0 0 0⟩

theorem no_failed_terminal
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (f g s r e p h m c n budget : Nat) (request : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (stored : Stored before) (terminal : Terminal request.value) :
    ¬∃ fault after, nodeBody f g s r e p h m c n budget request before = .failed fault after := by
  obtain ⟨result, actual, reads, checks, post, resident, retained, law, done⟩ :=
    complete formulas solver budget request initial ready available stored terminal
  rintro ⟨fault, after, failed⟩
  cases (done f g s r e p h m c n).symm.trans failed

theorem published_terminal
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before running : Caller width} {memos : Memos}
    (budget : Nat) (request owner : NodeRequest) (handle : Nat)
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (stored : Stored before)
    (started : beginNode request before = (handle, .evaluate owner, running)) (terminal : Terminal owner.value) :
    ∃ result, ∃ actual : NodeCall budget request before result (finishNode handle result running),
      NodeCallReads formulas solver actual memos memos ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver inventory before (finishNode handle result running) memos ∧
      Stored (finishNode handle result running) ∧ NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before =
          .done result (finishNode handle result running) := by
  obtain ⟨runningContext, ownerGood, key, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial ready available started
  have runningStored := stored.beginNode request
  rw [started] at runningStored
  obtain ⟨result, body, reads, checks, post, resident, retained, law, done⟩ :=
    complete formulas solver budget owner runningContext ownerGood.inherited ownerGood.input runningStored terminal
  have finished := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
    initial ready available started body post resident law
  let actual : NodeCall budget request before result (finishNode handle result running) := .evaluate started body
  have callChecks : Checks (nodeCallTrace actual) :=
    SourceCurrentAllocatedPartialChecksComposition.node_evaluate started body checks
  refine ⟨result, actual, .evaluate (started := started) reads, callChecks, finished.1,
    retained.finishNode handle result, finished.2.2, ?_⟩
  intro f g s r e p h m c n
  simp only [SourceCurrentAllocatedPartialWorker.nodeCall, started, done f g s r e p h m c n,
    SourceCurrentAllocatedPartialWorker.Outcome.bind]

end TerminalChecks

#print axioms TerminalChecks.empty_zero
#check @TerminalChecks.empty_zero
#print axioms TerminalChecks.union_members_opaque
#check @TerminalChecks.union_members_opaque
#print axioms TerminalChecks.mu_cleanup
#check @TerminalChecks.mu_cleanup
#print axioms TerminalChecks.no_failed_terminal
#check @TerminalChecks.no_failed_terminal
#print axioms TerminalChecks.published_terminal
#check @TerminalChecks.published_terminal
