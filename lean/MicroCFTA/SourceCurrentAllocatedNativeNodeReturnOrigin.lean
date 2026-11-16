import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Actual node completion origins

A returned node cell has an earlier finish instruction in the same trace.
The receipt retains the handle, request, payload, full states and counts.
It does not identify an earlier compiler dispatch for an arbitrary control.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin
open Cache InternedConstructorTemplates
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

private theorem lookup_returned_before {Key Request Answer : Type} [DecidableEq Key]
    (key : Key) (candidate : Request) (state : FlatMemoThunk.State Key Request Answer)
    (handle : Nat) (request : Request) (value : Answer)
    (stored : (FlatMemoThunk.lookupOrInsert key candidate state).2.cells handle =
      some ⟨request, .returned value⟩) :
    state.cells handle = some ⟨request, .returned value⟩ := by
  cases found : state.table key with
  | some existing => simpa only [FlatMemoThunk.lookupOrInsert, found] using stored
  | none =>
      by_cases same : handle = state.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, Cache.put] at stored
      · simpa only [FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored

private theorem evaluating_returned_before {Key Request Answer : Type}
    (state : FlatMemoThunk.State Key Request Answer) (changed handle : Nat)
    (request : Request) (value : Answer)
    (stored : (FlatMemoThunk.setStatus changed .evaluating state).cells handle =
      some ⟨request, .returned value⟩) :
    state.cells handle = some ⟨request, .returned value⟩ := by
  cases found : state.cells changed with
  | none => simpa only [FlatMemoThunk.setStatus, found] using stored
  | some cell =>
      by_cases same : handle = changed
      · subst handle
        simp [FlatMemoThunk.setStatus, found, Cache.put] at stored
      · simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored

private theorem demand_returned_before {Key Request Answer : Type}
    (state : FlatMemoThunk.State Key Request Answer) (demanded handle : Nat)
    (request : Request) (value : Answer)
    (stored : (FlatMemoThunk.demand demanded state).2.cells handle =
      some ⟨request, .returned value⟩) :
    state.cells handle = some ⟨request, .returned value⟩ := by
  cases found : state.cells demanded with
  | none => simpa only [FlatMemoThunk.demand, found] using stored
  | some cell =>
      cases cell with
      | mk original phase =>
          cases phase with
          | suspended =>
              exact evaluating_returned_before state demanded handle request value
                (by simpa only [FlatMemoThunk.demand, found] using stored)
          | evaluating | returned result =>
              simpa only [FlatMemoThunk.demand, found] using stored

private theorem finish_returned_before {Key Request Answer : Type}
    (state : FlatMemoThunk.State Key Request Answer) (finished handle : Nat)
    (result : Answer) (request : Request) (value : Answer)
    (stored : (FlatMemoThunk.finish finished result state).cells handle =
      some ⟨request, .returned value⟩) :
    state.cells handle = some ⟨request, .returned value⟩ ∨
      (handle = finished ∧ value = result ∧ state.cells handle = some ⟨request, .evaluating⟩) := by
  cases found : state.cells finished with
  | none => exact Or.inl (by simpa only [FlatMemoThunk.finish, found] using stored)
  | some cell =>
      cases cell with
      | mk original phase =>
          cases phase with
          | suspended | returned previous =>
              exact Or.inl (by simpa only [FlatMemoThunk.finish, found] using stored)
          | evaluating =>
              by_cases same : handle = finished
              · subst finished
                have cellSame : (⟨original, .returned result⟩ : FlatMemoThunk.Cell Request Answer) =
                    ⟨request, .returned value⟩ := by
                  apply Option.some.inj
                  simpa only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus,
                    Cache.put, ite_true] using stored
                have requestSame := congrArg FlatMemoThunk.Cell.request cellSame
                have valueSame := FlatMemoThunk.Status.returned.inj
                  (congrArg FlatMemoThunk.Cell.status cellSame)
                cases requestSame
                cases valueSame
                exact Or.inr ⟨rfl, rfl, found⟩
              · exact Or.inl (by
                  simpa only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus,
                    Cache.put, ite_eq_right same] using stored)

private theorem node_lookup_returned_before {width : Nat}
    (candidate : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (stored : (lookupNode width candidate state).2.nodes.cells handle = some ⟨request, .returned value⟩) :
    state.nodes.cells handle = some ⟨request, .returned value⟩ := by
  cases selected : SourceRecursiveIntersectionMemo.requestKey width candidate.domain candidate.left candidate.right with
  | none => simpa only [lookupNode, selected] using stored
  | some key =>
      exact lookup_returned_before key candidate state.nodes handle request value
        (by simpa only [lookupNode, selected] using stored)

private theorem node_demand_returned_before {width : Nat}
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (demanded handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (stored : (demandNode demanded state).2.nodes.cells handle = some ⟨request, .returned value⟩) :
    state.nodes.cells handle = some ⟨request, .returned value⟩ :=
  demand_returned_before state.nodes demanded handle request value stored

private theorem step_returned_origin [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (control next : Control Output) (before after : Checked width)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (stored : after.native.nodes.cells handle = some ⟨request, .returned value⟩) :
    before.native.nodes.cells handle = some ⟨request, .returned value⟩ ∨
      ∃ continuation : Code Symbol Guard Output,
        control = .code (.finishNode handle value continuation) ∧
        before.native.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  cases control with
  | edgeBody edge continuation =>
      have unchanged := SourceEqualityNativeDemandOperations.body_native edge continuation before
      rw [show body edge continuation before = .yielded next after from one] at unchanged
      have nativeSame : after.native = before.native := unchanged
      exact Or.inl (by simpa only [nativeSame] using stored)
  | code code =>
      cases code with
      | pure | fail =>
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
      | work job continuation | enter domain left right first second continuation | read name continuation | finishEdge finished result continuation =>
          have same := Outcome.yielded.inj (by
            simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, lift] using one)
          rcases same with ⟨rfl, rfl⟩
          exact Or.inl stored
      | optionalBinder pair bodyValue continuation =>
          cases produced : SourceRecursiveIntersectionMaybeMu.maybeMu pair bodyValue before.native.machine.heap with
          | pending pending heap =>
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                produced, lift] at one
              cases one
          | done result heap =>
              have same := Outcome.yielded.inj (by
                simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                  produced, lift] using one)
              rcases same with ⟨rfl, rfl⟩
              exact Or.inl stored
      | finishNode finished result continuation =>
          have same := Outcome.yielded.inj (by
            simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, lift] using one)
          rcases same with ⟨rfl, rfl⟩
          rcases finish_returned_before before.native.nodes finished handle result request value stored with
            old | ⟨rfl, rfl, running⟩
          · exact Or.inl old
          · exact Or.inr ⟨continuation, rfl, running⟩
      | node candidate continuation =>
          cases selected : lookupNode width candidate before.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  have same := Outcome.yielded.inj (by
                    simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                      selected, lift] using one)
                  rcases same with ⟨rfl, rfl⟩
                  exact Or.inl (node_lookup_returned_before candidate before.native handle request value
                    (by simpa only [selected] using stored))
              | memoized demanded =>
                  cases demandedEq : demandNode demanded chosen with
                  | mk observation running =>
                      cases observation with
                      | absent | busy =>
                          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                            selected, demandedEq, lift] at one
                          cases one
                      | ready result | evaluate actual =>
                          have same := Outcome.yielded.inj (by
                            simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                              selected, demandedEq, lift] using one)
                          rcases same with ⟨rfl, rfl⟩
                          have chosenStored := node_demand_returned_before chosen demanded handle request value
                            (by simpa only [demandedEq] using stored)
                          exact Or.inl (node_lookup_returned_before candidate before.native handle request value
                            (by simpa only [selected] using chosenStored))
      | edge candidate continuation =>
          cases selected : lookupEdge width candidate before.native with
          | mk demanded chosen =>
              have chosenNodes : chosen.nodes = before.native.nodes := by
                have unchanged : (lookupEdge width candidate before.native).2.nodes = before.native.nodes := rfl
                simpa only [selected] using unchanged
              cases demandedEq : demandEdge demanded chosen with
              | mk observation running =>
                  have runningNodes : running.nodes = chosen.nodes := by
                    have unchanged : (demandEdge demanded chosen).2.nodes = chosen.nodes := rfl
                    simpa only [demandedEq] using unchanged
                  cases observation with
                  | absent | busy =>
                      simp only [SourceEqualityNativeDemand.step, selected, demandedEq] at one
                      cases one
                  | ready result | evaluate actual =>
                      have same := Outcome.yielded.inj (by
                        simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                          selected, demandedEq, lift] using one)
                      rcases same with ⟨rfl, rfl⟩
                      exact Or.inl (by simpa only [runningNodes, chosenNodes] using stored)

private theorem trace_returned_or_finish [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    {count : Nat} {control rest : Control Output} {before after : Checked width}
    (actual : Trace count control before rest after) :
    ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard),
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ →
      before.native.nodes.cells handle = some ⟨request, .returned value⟩ ∨
      ∃ (prefixCount suffixCount : Nat) (beforeFinish : Checked width)
        (next : Code Symbol Guard Output),
        count = prefixCount + 1 + suffixCount ∧
        Trace prefixCount control before (.code (.finishNode handle value next)) beforeFinish ∧
        beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
        Trace 1 (.code (.finishNode handle value next)) beforeFinish (.code next)
          { beforeFinish with native := finishNode handle value beforeFinish.native } ∧
        ({ beforeFinish with native := finishNode handle value beforeFinish.native } : Checked width).native.nodes.cells
          handle = some ⟨request, .returned value⟩ ∧
        Trace suffixCount (.code next)
          { beforeFinish with native := finishNode handle value beforeFinish.native } rest after := by
  induction actual with
  | refl =>
      intro handle request value stored
      exact Or.inl stored
  | cons control before next middle rest after count inputs one tail ih =>
      intro handle request value stored
      rcases ih handle request value stored with earlier | ⟨used, remaining, origin, continuation,
          total, prefixActual, running, finishActual, finished, suffixActual⟩
      · rcases step_returned_origin control next before middle one handle request value earlier with
          original | ⟨continuation, same, running⟩
        · exact Or.inl original
        · subst control
          have endpoints := Outcome.yielded.inj one
          rcases endpoints with ⟨rfl, rfl⟩
          have finished : ({ before with native := finishNode handle value before.native } : Checked width).native.nodes.cells
              handle = some ⟨request, .returned value⟩ := by
            change (FlatMemoThunk.finish handle value before.native.nodes).cells handle = _
            simpa only [FlatMemoThunk.finish, running] using
              (FlatMemoThunk.setStatus_cell handle (.returned value) before.native.nodes
                ⟨request, .evaluating⟩ running)
          exact Or.inr ⟨0, count, before, continuation, by omega, .refl _ _, running,
            .cons _ _ _ _ _ _ 0 inputs one (.refl _ _), finished, tail⟩
      · exact Or.inr ⟨used + 1, remaining, origin, continuation, by omega,
          .cons control before next middle _ origin used inputs one prefixActual,
          running, finishActual, finished, suffixActual⟩

/-- A returned cell from complete empty initialization has an actual same-trace finish prefix. -/
theorem returned_node_cell_finish_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (control rest : Control Output) (after : Checked width) (fuel count : Nat)
    (bounded : count ≤ fuel)
    (actual : Trace count control ⟨initial width machine, operations⟩ rest after)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (stored : after.native.nodes.cells handle = some ⟨request, .returned value⟩) :
    ∃ (prefixCount suffixCount : Nat) (beforeFinish : Checked width)
      (next : Code Symbol Guard Output),
      count = prefixCount + 1 + suffixCount ∧ prefixCount < count ∧ prefixCount < fuel ∧
      Trace prefixCount control ⟨initial width machine, operations⟩
        (.code (.finishNode handle value next)) beforeFinish ∧
      beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      Trace 1 (.code (.finishNode handle value next)) beforeFinish (.code next)
        { beforeFinish with native := finishNode handle value beforeFinish.native } ∧
      ({ beforeFinish with native := finishNode handle value beforeFinish.native } : Checked width).native.nodes.cells
        handle = some ⟨request, .returned value⟩ ∧
      Trace suffixCount (.code next)
        { beforeFinish with native := finishNode handle value beforeFinish.native } rest after := by
  rcases trace_returned_or_finish actual handle request value stored with impossible |
    ⟨used, remaining, origin, continuation, total, prefixActual, running, finishActual, finished, suffixActual⟩
  · cases impossible
  · exact ⟨used, remaining, origin, continuation, total, by omega, by omega,
      prefixActual, running, finishActual, finished, suffixActual⟩

end MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin
open Cache InternedConstructorTemplates
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
set_option autoImplicit false

theorem returned_node_cell_or_finish_prefix [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    {count : Nat} {control rest : Control Output} {before after : Checked width}
    (actual : Trace count control before rest after) :
    ∀ (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard),
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ →
      before.native.nodes.cells handle = some ⟨request, .returned value⟩ ∨
      ∃ (prefixCount suffixCount : Nat) (beforeFinish : Checked width)
        (next : Code Symbol Guard Output),
        count = prefixCount + 1 + suffixCount ∧
        Trace prefixCount control before (.code (.finishNode handle value next)) beforeFinish ∧
        beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
        Trace 1 (.code (.finishNode handle value next)) beforeFinish (.code next)
          { beforeFinish with native := finishNode handle value beforeFinish.native } ∧
        ({ beforeFinish with native := finishNode handle value beforeFinish.native } : Checked width).native.nodes.cells
          handle = some ⟨request, .returned value⟩ ∧
        Trace suffixCount (.code next)
          { beforeFinish with native := finishNode handle value beforeFinish.native } rest after
 := trace_returned_or_finish actual

end MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin
