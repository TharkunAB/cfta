import MicroCFTA.SourceEqualityNativeDemandTraceSplit
import MicroCFTA.SourceRecursiveIntersectionNativeShape
import MicroCFTA.SourceRecursiveIntersectionNativeObservations

/-!
# Actual completed checked node calls

Completion selects a direct body, an unchanged ready hit, or the actual
demanded body followed by its original finish handle. The readback retains
complete states and exact trace lengths. It does not assume result
provenance or future validity. Running-cell preservation through the body
is a separate invariant.
-/
namespace MicroCFTA.SourceEqualityNativeDemandNodeReadback
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State

/-- An actual ready demand after selection comes from an original returned cell and has no state effects. -/
theorem ready_selection (request : NodeRequest Symbol Guard) (before chosen current : Native width Symbol Guard)
    (handle : Nat) (value : Value Symbol Guard)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, current)) :
    ∃ key original, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key ∧
      before.nodes.table key = some handle ∧ before.nodes.cells handle = some ⟨original, .returned value⟩ ∧
      chosen = before ∧ current = before := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simp only [lookupNode, requested] at selected; cases selected
  | some key =>
      cases published : before.nodes.table key with
      | none =>
          have same := Prod.mk.inj (by simpa only [lookupNode, requested, FlatMemoThunk.lookupOrInsert, published] using selected)
          have handles := NodeSelection.memoized.inj same.1
          rcases handles with rfl
          rcases same.2 with rfl
          simp [demandNode, FlatMemoThunk.demand, Cache.put] at demanded
      | some actualHandle =>
          have same := Prod.mk.inj (by simpa only [lookupNode, requested, FlatMemoThunk.lookupOrInsert, published] using selected)
          have handles := NodeSelection.memoized.inj same.1
          rcases handles with rfl
          rcases same.2 with rfl
          obtain ⟨original, stored, retained⟩ := SourceRecursiveIntersectionNative.demandNode_ready actualHandle before current value demanded
          exact ⟨key, original, rfl, published, stored, rfl, retained⟩

/-- A node finish frame consumes exactly one step at its actual updated full state. -/
theorem finish_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (handle : Nat) (result : Value Symbol Guard) (next : Code Symbol Guard Output)
    (before after : State width) (value : Output)
    (trace : Steps fuel (.code (.finishNode handle result next)) before (.code (.pure value)) after) :
    ∃ rest, fuel = rest + 1 ∧ Steps rest (.code next)
      {before with native := SourceRecursiveIntersectionThunks.finishNode handle result before.native}
      (.code (.pure value)) after := by
  cases fuel with
  | zero => cases (steps_zero _ _ _ _ trace).1
  | succ fuel =>
      obtain ⟨control, current, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      have same := Outcome.yielded.inj one
      rcases same.1 with rfl
      rcases same.2 with rfl
      exact ⟨fuel, rfl, tail⟩

/-- The three possible completed node-call branches retain actual source states and body traces. -/
inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before : State width) : Value Symbol Guard → State width → Nat → Prop where
  | direct (fuel : Nat) (after : State width) (value : Value Symbol Guard)
      (unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
      (body : Steps fuel (.code (compileNode request)) before (.code (.pure value)) after) :
      Call request before value after (fuel + 1)
  | ready (key : IntersectionFlatMemoKeyDomain.Triple width) (handle : Nat) (original : NodeRequest Symbol Guard)
      (value : Value Symbol Guard)
      (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
      (published : before.native.nodes.table key = some handle)
      (returned : before.native.nodes.cells handle = some ⟨original, .returned value⟩) :
      Call request before value before 1
  | started (fuel handle : Nat) (chosen running : Native width Symbol Guard) (actual : NodeRequest Symbol Guard)
      (middle : State width) (value : Value Symbol Guard)
      (selected : lookupNode width request before.native = (.memoized handle, chosen))
      (demanded : demandNode handle chosen = (.evaluate actual, running))
      (suspended : chosen.nodes.cells handle = some ⟨actual, .suspended⟩)
      (evaluating : running.nodes.cells handle = some ⟨actual, .evaluating⟩)
      (machine : running.machine = before.native.machine)
      (body : Steps fuel (.code (compileNode actual)) ⟨running, before.operations⟩ (.code (.pure value)) middle) :
      Call request before value
        {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native} (fuel + 2)

/-- An actual completed node trace derives its selected branch, body, and exact finish state. -/
theorem of_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : State width) (value : Value Symbol Guard)
    (trace : Steps fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Call request before value after fuel := by
  cases fuel with
  | zero => cases (steps_zero _ _ _ _ trace).1
  | succ fuel =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          cases selection with
          | direct actual =>
              obtain ⟨actualSame, chosenSame⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected
              subst actual
              subst chosen
              have same := Outcome.yielded.inj (by simpa only [SourceEqualityNativeDemand.step, requestNode,
                SourceRecursiveIntersectionNative.step, selected, lift] using one)
              rcases same.1 with rfl
              rcases same.2 with rfl
              have unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none := by
                cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
                | none => rfl
                | some key => simp only [lookupNode, requested] at selected; cases selected
              exact .direct fuel after value unresolved (by simpa only [code_bind_pure] using tail)
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [SourceEqualityNativeDemand.step, requestNode, SourceRecursiveIntersectionNative.step,
                        selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      have same := Outcome.yielded.inj (by simpa only [SourceEqualityNativeDemand.step, requestNode,
                        SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      obtain ⟨rfl, rfl, rfl⟩ := pure_trace fuel result value ⟨running, before.operations⟩ after tail
                      obtain ⟨key, original, requested, published, returned, _, retained⟩ :=
                        ready_selection request before.native chosen running handle result selected demanded
                      simpa only [retained] using Call.ready (request := request) (before := before)
                        key handle original result requested published returned
                  | evaluate actual =>
                      have same := Outcome.yielded.inj (by simpa only [SourceEqualityNativeDemand.step, requestNode,
                        SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      obtain ⟨inner, outer, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
                        (.code (compileNode actual)) (fun result => .finishNode handle result (.pure result))
                        ⟨running, before.operations⟩ after value tail
                      obtain ⟨remaining, frameCount, finalTrace⟩ := finish_trace outer handle result (.pure result) middle after value frameTrace
                      obtain ⟨rfl, rfl, rfl⟩ := pure_trace remaining result value _ after finalTrace
                      have total : inner + 2 = fuel + 1 := by omega
                      rw [← total]
                      have cells := SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded
                      have runningMachine : running.machine = chosen.machine := by
                        simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen
                      have chosenMachine : chosen.machine = before.native.machine := by
                        simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
                      exact .started inner handle chosen running actual middle result selected demanded cells.1 cells.2
                        (runningMachine.trans chosenMachine) bodyTrace

/-- Actual bounded node completion derives exact branch readback below the original bound. -/
theorem of_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : State width) (value : Value Symbol Guard)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    ∃ steps, steps < fuel ∧ Call request before value after steps := by
  obtain ⟨steps, bounded, trace⟩ := done_trace fuel _ before after value done
  exact ⟨steps, bounded, of_trace steps request before after value trace⟩

end MicroCFTA.SourceEqualityNativeDemandNodeReadback
