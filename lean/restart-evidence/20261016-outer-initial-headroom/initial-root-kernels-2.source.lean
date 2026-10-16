import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.InitialRootResourceChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot (initialNodes initialEdges)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Syntax" => InternedNestedConstruction.Syntax Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem demand_table {MemoKey Request Result : Type} (handle : Nat) (memo : FlatMemoThunk.State MemoKey Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase, FlatMemoThunk.setStatus]

private theorem finish_table {MemoKey Request Result : Type} (handle : Nat) (result : Result) (memo : FlatMemoThunk.State MemoKey Request Result) :
    (FlatMemoThunk.finish handle result memo).table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk request status => cases status <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

private theorem node_warm
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {width budget : Nat} {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {request : NodeRequest} {before after : Caller width} {result : Node} {memos : EndpointMemoGateTrace.Memos}
    (actual : NodeCall budget request before result after)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) :
    ∃ handle, beginNode request after = (handle, .ready result, after) := by
  cases actual with
  | hit started =>
      obtain ⟨same, _available, _law⟩ := SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request _ initial.sound
        initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available _ _ _ started
      subst after
      exact ⟨_, started⟩
  | @evaluate request before handle running owner result middle started body =>
      obtain ⟨runningContext, _owner, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
        initial inherited available started
      have frame := SourceCurrentAllocatedPartialFrames.node_body body
        (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
      have returned := finishNode_returned handle owner result middle (frame.node_running handle owner cell)
      have published : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
        change (FlatMemoThunk.demand _ _).2.table _ = _
        rw [demand_table]
        exact FlatMemoThunk.lookup_stored _ _ _
      rw [started] at published
      have finalPublished : (finishNode handle result middle).nodeResults.table request.key = some handle := by
        change (FlatMemoThunk.finish handle result middle.nodeResults).table request.key = some handle
        rw [finish_table]
        exact frame.node_keys request.key handle published
      exact ⟨handle, beginNode_ready request owner _ handle result finalPublished returned⟩

/-- One constructed root return retains every conclusion and has a literal zero-bound warm repeat. -/
def Reduction (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat) (cache : Cache.State Key) (value : Node) (heap : Heap) : Prop :=
  ∃ result after next final,
    SourceCurrentAllocatedPartialWorkerCompletion.StableRun
      (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
        ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) result after ∧
    ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
      NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next (caller (bits + 2) cache heap) after final ∧
      Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
      NodeCertificate ⟨emptyValue cache, value⟩ result ∧
      WorkBounds heap after.checked.native.machine.heap (initialNodes value) (initialEdges value) ∧
      Headroom bits after.checked.native.machine.heap 0 0 ∧
      (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) ∧
      after.checked.native.machine.heap.nodes.next ≤ heap.nodes.next + initialNodes value ∧
      after.checked.native.machine.heap.edges.next ≤ heap.edges.next + initialEdges value ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 budget
        ⟨emptyValue cache, value⟩ after = .done result after ∧
      WorkBounds after.checked.native.machine.heap after.checked.native.machine.heap 0 0

/-- Initial field history and source syntax construct the full reduction and its warm repeat. -/
theorem constructed_then_warm
    (bits : Nat) {initial cache : Cache.State Key} {originals : List Guard}
    (history : History initial cache originals) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Reduction bits formulas solver budget cache value heap := by
  obtain ⟨value, heap, built, result, after, next, final, stable, actual, reads, checks, post,
    output, stored, narrow, certificate, work, finalRoom, language⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot.constructed_root bits history valid expression domain covered formulas solver budget room
  obtain ⟨initialContext, identity, same, inherited, available, _free, _original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed (bits + 2) history valid expression covered value heap built formulas solver
  have ready : EqReady (caller (bits + 2) cache heap).checked.operations.constraints (emptyValue cache) := by
    rw [same]; exact inherited
  obtain ⟨handle, warm⟩ := node_warm formulas solver actual initialContext ready available
  have supplies := work.next_le
  exact ⟨value, heap, built, result, after, next, final, stable, actual, reads, checks, post,
    output, stored, narrow, certificate, work, finalRoom, language, supplies.1, supplies.2,
    SourceCurrentAllocatedPartialWorker.nodeCall_ready 0 0 0 0 0 0 0 0 0 0 budget _ _ _ handle result warm,
    WorkBounds.refl _⟩

/-- Actual field preparation supplies all source fields before the same initial-only root theorem. -/
theorem prepared_fields_and_root
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      (∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
        ∃ loaded, SourceEqualityConstraintFieldLookup.load original cache = .ok (some loaded) ∧
          SourceEqualityConjoinAllocation.readback loaded = original ∧ EqReady cache loaded.stored ∧
          SourceEqualityPhysicalPayload.read original.equalities = .ok loaded.stored.payload) ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        Reduction bits formulas solver budget cache value heap := by
  let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
  obtain ⟨fields, finalCache, receipt⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initial valid cached
  have same : cache = finalCache := congrArg Prod.snd receipt.done
  have exactReceipt : SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache := by simpa only [same] using receipt
  exact ⟨fields, exactReceipt, fun original member => exactReceipt.load original member,
    constructed_then_warm bits exactReceipt.history valid expression domain (fun _ member => member) formulas solver budget room⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- The public prepared endpoint retains field history, exact root semantics, and both final supplies. -/
theorem prepared_endpoint_supplies
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap result after next final,
        InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
        Post formulas solver next (caller (bits + 2) cache heap) after final ∧ Stored after ∧
        NodeCertificate ⟨emptyValue cache, value⟩ result ∧
        WorkBounds heap after.checked.native.machine.heap (initialNodes value) (initialEdges value) ∧
        after.checked.native.machine.heap.nodes.next ≤ heap.nodes.next + initialNodes value ∧
        after.checked.native.machine.heap.edges.next ≤ heap.edges.next + initialEdges value ∧
        (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) := by
  obtain ⟨fields, receipt, value, heap, built, result, after, next, final, _stable, _actual, _reads, _checks, post,
    _output, stored, _narrow, certificate, work, _finalRoom, language⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot.prepared_root bits initial valid expression domain cached formulas solver budget room
  have supplies := work.next_le
  exact ⟨fields, receipt, value, heap, result, after, next, final, built, post, stored, certificate,
    work, supplies.1, supplies.2, language⟩

/-- A nonempty ordinary source row with an arbitrary full guard needs no positive conjunction budget. -/
theorem guarded_nullary_budget_zero
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial) (symbol : Symbol) (guard : Guard)
    (cached : SourceEqualityGuardReadback.Cached guard.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (room : ∀ value heap,
      InternedFreshOrdinaryConstruction.build (.node [.mk symbol guard []]) [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    let expression : Syntax := .node [.mk symbol guard []]
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      (∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
        ∃ loaded, SourceEqualityConstraintFieldLookup.load original cache = .ok (some loaded) ∧
          SourceEqualityConjoinAllocation.readback loaded = original ∧ EqReady cache loaded.stored ∧
          SourceEqualityPhysicalPayload.read original.equalities = .ok loaded.stored.payload) ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        Reduction bits formulas solver 0 cache value heap := by
  apply prepared_fields_and_root bits initial valid (.node [.mk symbol guard []]) (.ordinary (.cons .nil .nil))
    (fun original member => ?_) formulas solver 0 room
  simp only [SourceEqualityConstraintOrigins.guards, SourceEqualityConstraintOrigins.edgeGuards,
    SourceEqualityConstraintOrigins.childGuards, List.nil_append, List.mem_singleton] at member
  subst original
  exact cached

#print axioms Reduction
#check @Reduction
#print axioms constructed_then_warm
#check @constructed_then_warm
#print axioms prepared_fields_and_root
#check @prepared_fields_and_root
#print axioms prepared_endpoint_supplies
#check @prepared_endpoint_supplies
#print axioms guarded_nullary_budget_zero
#check @guarded_nullary_budget_zero
end MicroCFTA.InitialRootResourceChecks
