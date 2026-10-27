import MicroCFTA.SourceEqualityNativeDemandAcceptedReceipt
import MicroCFTA.SourceEqualityNativeDemandWalkExecution

/-!
# Actual accepted completion derives its child executions

Completion determines the actual ordered child traces and final constructor
state. Each child trace is shorter than the parent execution bound. These
facts support induction on actual completed execution. The semantic theorem
retains checks only for child walks from its actual prefix state.
-/
namespace MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Actual constructor completion identifies its full result and returned checked state at any bound. -/
theorem work_observation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard Output) (fuel : Nat) (before after : State width) (value : Output)
    (done : execute fuel (.code (.work job .pure)) before = .done value after) :
    let built := run job before.native.machine.heap
    value = built.1 ∧ after = {before with native := advance before.native {before.native.machine with heap := built.2}} := by
  let built := run job before.native.machine.heap
  let final : State width := {before with native := advance before.native {before.native.machine with heap := built.2}}
  have actual : execute 2 (.code (.work job .pure)) before = .done built.1 final := rfl
  have first := done_stable fuel 2 _ before after value done
  have second := done_stable 2 fuel _ before final built.1 actual
  rw [Nat.add_comm 2 fuel] at second
  exact Outcome.done.inj (first.symm.trans second)

/-- Actual accepted-code completion derives its ordered child runs and exact final constructor. -/
theorem children_observation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (combined : Allocated) (fuel : Nat)
    (before after : State width) (result : EdgeValue Symbol Guard)
    (done : execute fuel (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
      before = .done result after) :
    ∃ values middle count, count < fuel ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children) before values middle count ∧
      result = (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
        middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).2}} := by
  obtain ⟨total, bounded, trace⟩ := done_trace fuel _ before after result done
  obtain ⟨inner, outer, values, middle, count, walked, built⟩ := steps_bind_inverse total
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children)))
    (fun values => .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)
    before after result trace
  have outputs := work_observation _ (outer + 1) middle after result (trace_done outer _ middle after result built)
  exact ⟨values, middle, inner, by omega,
    SourceEqualityNativeDemandWalkExecution.trace_walk _ _ inner before middle values walked, outputs⟩

/-- Actual ready-body completion derives child completion bounds below the original parent bound. -/
theorem body_observation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state after : State width) (first second combined : Allocated)
    (fuel : Nat) (result : EdgeValue Symbol Guard)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (done : execute fuel (.edgeBody request .pure) state = .done result after) :
    ∃ values middle count, count + 1 < fuel ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)
        {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length state.operations).2} values middle count ∧
      result = (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
        middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).2}} := by
  cases fuel with
  | zero => cases done
  | succ fuel =>
      have one := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        state arity first second combined left right accepted
      simp only [code_bind_pure] at one
      have tail : execute fuel (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
          {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
            request.left.children.length request.right.children.length state.operations).2} = .done result after := by
        simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, one] using done
      obtain ⟨values, middle, count, bounded, walk, fields⟩ := children_observation request combined fuel _ after result tail
      exact ⟨values, middle, count, by omega, walk, fields⟩

/-- Bounded child checks at the actual prefix state derive provenance of the observed accepted result. -/
theorem body_produced_of_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state after : State width) (first second combined : Allocated)
    (fuel : Nat) (result : EdgeValue Symbol Guard)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (done : execute fuel (.edgeBody request .pure) state = .done result after)
    (calls : ∀ (values : List (Value Symbol Guard)) (middle : State width) (count : Nat)
      (walk : SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)
        {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length state.operations).2} values middle count),
      count + 1 < fuel → SourceEqualityNativeDemandChildWalk.Checks (SourceEqualityPCSGuard.holds formulas solver) request.domain walk) :
    EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) after.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧ EdgeResident after.native.machine.heap result := by
  obtain ⟨values, middle, count, bounded, raw, rfl, rfl⟩ :=
    body_observation request state after first second combined fuel result arity left right accepted done
  have walk := SourceEqualityNativeDemandChildWalk.certify (SourceEqualityPCSGuard.holds formulas solver) request.domain _ _ _ _ count raw
    (calls values middle count raw bounded)
  have checked := SourceEqualityNativeDemandAcceptedReceipt.body_produced formulas solver request state middle first second combined
    values count valid heapReady inputs leftCached rightCached arity symbols left right accepted walk
  exact ⟨checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

end MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
