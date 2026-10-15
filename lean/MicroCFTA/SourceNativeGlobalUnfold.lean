import MicroCFTA.SourceConstructorGlobalUnfoldBuild
import MicroCFTA.SourceRecursiveIntersectionNative

/-!
# Global unfolding events through native instructions

The executor expands constructor work and the fixed optional-binder callback.
Each native instruction retains its original control and memo effects.
The execution bound counts native instructions as in the original executor.
These records represent complete resident operands. They do not represent
the delayed Haskell computations that can produce those operands.
-/
namespace MicroCFTA.SourceNativeGlobalUnfold
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceGlobalUnfold (Event NoGlobal)

/-- Execute one native instruction and retain its actual constructor events. -/
def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    SourceRecursiveIntersectionNative.Outcome width Symbol Guard A × List (Event Symbol Guard) :=
  match code with
  | .pure value => (.done value state, [])
  | .fail failure => (.failed failure state, [])
  | .work job next =>
      let actual := SourceConstructorGlobalUnfold.work job state.machine.heap
      (.yielded (next actual.1.1) (advance state {state.machine with heap := actual.1.2}), actual.2)
  | .enter domain left right first second next =>
      let entered := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
      (.yielded (next entered.1) (advance state {state.machine with domains := entered.2}), [])
  | .read name next => (.yielded (next (SourcePreparedSharedRows.read state.machine.heap name)) state, [])
  | .optionalBinder key body next =>
      let actual := SourceConstructorGlobalUnfold.maybeMu key body state.machine.heap
      match actual.1 with
      | .done value after => (.yielded (next value) (advance state {state.machine with heap := after}), actual.2)
      | .pending pending after => (.blocked (.constructor pending) code (advance state {state.machine with heap := after}), actual.2)
  | .node request next =>
      let selected := lookupNode width request state
      match selected.1 with
      | .direct actual => (.yielded ((compileNode actual).bind next) selected.2, [])
      | .memoized handle =>
          let demanded := demandNode handle selected.2
          match demanded.1 with
          | .absent => (.blocked (.absentNode handle) code demanded.2, [])
          | .busy => (.blocked (.nodeBusy handle) code demanded.2, [])
          | .ready value => (.yielded (next value) demanded.2, [])
          | .evaluate actual =>
              (.yielded ((compileNode actual).bind fun value => .finishNode handle value (next value)) demanded.2, [])
  | .edge request next =>
      let selected := lookupEdge width request state
      let demanded := demandEdge selected.1 selected.2
      match demanded.1 with
      | .absent => (.blocked (.absentEdge selected.1) code demanded.2, [])
      | .busy => (.blocked (.edgeBusy selected.1) code demanded.2, [])
      | .ready value => (.yielded (next value) demanded.2, [])
      | .evaluate actual =>
          (.yielded ((compileEdge emptyGuard conjoin actual).bind fun value => .finishEdge selected.1 value (next value)) demanded.2, [])
  | .finishNode handle value next => (.yielded next (SourceRecursiveIntersectionThunks.finishNode handle value state), [])
  | .finishEdge handle value next => (.yielded next (SourceRecursiveIntersectionThunks.finishEdge handle value state), [])

/-- Removing events gives the exact original native instruction outcome. -/
theorem step_erase [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (step emptyGuard conjoin code state).1 = SourceRecursiveIntersectionNative.step emptyGuard conjoin code state := by
  cases code with
  | pure | fail | enter | read | finishNode | finishEdge => rfl
  | work job next =>
      simp only [step, SourceConstructorGlobalUnfold.work_erase, SourceRecursiveIntersectionNative.step]
  | optionalBinder key body next =>
      simp only [step, SourceConstructorGlobalUnfold.maybeMu_erase]
      cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap <;>
        simp only [actual, SourceRecursiveIntersectionNative.step]
  | node request next =>
      cases selected : lookupNode width request state with
      | mk selection current =>
          cases selection with
          | direct actual => simp only [step, SourceRecursiveIntersectionNative.step, selected]
          | memoized handle =>
              cases demanded : demandNode handle current with
              | mk observation final =>
                  cases observation <;> simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded]
  | edge request next =>
      cases selected : lookupEdge width request state with
      | mk handle current =>
          cases demanded : demandEdge handle current with
          | mk observation final =>
              cases observation <;> simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded]

/-- Each actual native instruction has no global unfolding action on resident inputs. -/
theorem step_silent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    NoGlobal (step emptyGuard conjoin code state).2 := by
  have empty : NoGlobal ([] : List (Event Symbol Guard)) := by intro event member; cases member
  cases code with
  | pure | fail | enter | read | finishNode | finishEdge => exact empty
  | work job next => exact SourceConstructorGlobalUnfold.work_silent job state.machine.heap
  | optionalBinder key body next =>
      have silent := SourceConstructorGlobalUnfold.maybeMu_silent key body state.machine.heap
      cases actual : SourceConstructorGlobalUnfold.maybeMu key body state.machine.heap with
      | mk outcome events =>
          rw [actual] at silent
          cases outcome <;> simpa only [step, actual] using silent
  | node request next =>
      cases selected : lookupNode width request state with
      | mk selection current =>
          cases selection with
          | direct actual => simpa only [step, selected] using empty
          | memoized handle =>
              cases demanded : demandNode handle current with
              | mk observation final =>
                  cases observation <;> simpa only [step, selected, demanded] using empty
  | edge request next =>
      cases selected : lookupEdge width request state with
      | mk handle current =>
          cases demanded : demandEdge handle current with
          | mk observation final =>
              cases observation <;> simpa only [step, selected, demanded] using empty

/-- A bounded run retains every event before its exact terminal observation. -/
def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Nat → Code Symbol Guard A → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      SourceRecursiveIntersectionNative.Outcome width Symbol Guard A × List (Event Symbol Guard)
  | 0, code, state => (.yielded code state, [])
  | fuel + 1, code, state =>
      let actual := step emptyGuard conjoin code state
      match actual.1 with
      | .yielded next after =>
          let rest := execute emptyGuard conjoin fuel next after
          (rest.1, actual.2 ++ rest.2)
      | .done value after => (.done value after, actual.2)
      | .failed failure after => (.failed failure after, actual.2)
      | .blocked reason next after => (.blocked reason next after, actual.2)

/-- Erasure preserves the original bound, continuation, and all native memo cells. -/
theorem execute_erase [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (execute emptyGuard conjoin fuel code state).1 = SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel code state := by
  induction fuel generalizing code state with
  | zero => rfl
  | succ fuel ih =>
      simp only [execute]
      cases actual : step emptyGuard conjoin code state with
      | mk outcome events =>
          have erased := step_erase emptyGuard conjoin code state
          rw [actual] at erased
          simp only [SourceRecursiveIntersectionNative.execute, ← erased]
          cases outcome with
          | yielded next after => exact ih next after
          | done | failed | blocked => rfl

/-- Every bounded native run derives absence of global unfolding actions. -/
theorem execute_silent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    NoGlobal (execute emptyGuard conjoin fuel code state).2 := by
  induction fuel generalizing code state with
  | zero => intro event member; cases member
  | succ fuel ih =>
      have silent := step_silent emptyGuard conjoin code state
      cases actual : step emptyGuard conjoin code state with
      | mk outcome events =>
          rw [actual] at silent
          simp only [execute, actual]
          cases outcome with
          | yielded next after =>
              exact silent.append (ih next after)
          | done | failed | blocked => exact silent

/-- Native node publication does not change the constructor heap. -/
theorem lookupNode_heap (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (lookupNode width request state).2.machine.heap = state.machine.heap := by
  unfold lookupNode
  split <;> rfl

/-- Native edge publication does not change the constructor heap. -/
theorem lookupEdge_heap (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (lookupEdge width request state).2.machine.heap = state.machine.heap := rfl

/-- Beginning a native node thunk does not change the constructor heap. -/
theorem demandNode_heap (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (demandNode handle state).2.machine.heap = state.machine.heap := rfl

/-- Beginning a native edge thunk does not change the constructor heap. -/
theorem demandEdge_heap (handle : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (demandEdge handle state).2.machine.heap = state.machine.heap := rfl

/-- Each native event list executes its actual constructor primitives. -/
theorem step_runs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state.machine.heap, memo⟩
      ⟨(step emptyGuard conjoin code state).1.state.machine.heap, memo⟩ (step emptyGuard conjoin code state).2 := by
  have empty : SourceGlobalUnfold.Runs ⟨state.machine.heap, memo⟩ ⟨state.machine.heap, memo⟩ [] := .nil _
  cases code with
  | pure | fail | enter | read | finishNode | finishEdge => exact empty
  | work job next => exact SourceConstructorGlobalUnfold.work_runs job state.machine.heap memo
  | optionalBinder key body next =>
      have traced := SourceConstructorGlobalUnfold.maybeMu_runs key body state.machine.heap memo
      cases actual : SourceConstructorGlobalUnfold.maybeMu key body state.machine.heap with
      | mk outcome events =>
          rw [actual] at traced
          cases outcome <;> simpa only [step, actual, InternedNestedConstruction.Outcome.state,
            SourceRecursiveIntersectionNative.Outcome.state, advance] using traced
  | node request next =>
      cases selected : lookupNode width request state with
      | mk selection current =>
          have currentHeap : current.machine.heap = state.machine.heap := by
            simpa only [selected] using lookupNode_heap request state
          cases selection with
          | direct actual => simpa only [step, selected, SourceRecursiveIntersectionNative.Outcome.state, currentHeap] using empty
          | memoized handle =>
              cases demanded : demandNode handle current with
              | mk observation final =>
                  have finalHeap : final.machine.heap = state.machine.heap := by
                    have retained := demandNode_heap handle current
                    simpa only [demanded, currentHeap] using retained
                  cases observation <;>
                    simpa only [step, selected, demanded, SourceRecursiveIntersectionNative.Outcome.state, finalHeap] using empty
  | edge request next =>
      cases selected : lookupEdge width request state with
      | mk handle current =>
          have currentHeap : current.machine.heap = state.machine.heap := by
            simpa only [selected] using lookupEdge_heap request state
          cases demanded : demandEdge handle current with
          | mk observation final =>
              have finalHeap : final.machine.heap = state.machine.heap := by
                have retained := demandEdge_heap handle current
                simpa only [demanded, currentHeap] using retained
              cases observation <;>
                simpa only [step, selected, demanded, SourceRecursiveIntersectionNative.Outcome.state, finalHeap] using empty

/-- A bounded native execution derives an operational primitive trace at its exact heap. -/
theorem execute_runs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state.machine.heap, memo⟩
      ⟨(execute emptyGuard conjoin fuel code state).1.state.machine.heap, memo⟩ (execute emptyGuard conjoin fuel code state).2 := by
  induction fuel generalizing code state with
  | zero => exact .nil _
  | succ fuel ih =>
      have traced := step_runs emptyGuard conjoin code state memo
      cases actual : step emptyGuard conjoin code state with
      | mk outcome events =>
          rw [actual] at traced
          simp only [execute, actual]
          cases outcome with
          | yielded next after => exact traced.append (ih next after)
          | done | failed | blocked => exact traced

/-- The original native run has a derived operational trace with no global unfold call. -/
theorem execute_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    ∃ events, SourceGlobalUnfold.Runs ⟨state.machine.heap, memo⟩
      ⟨(SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel code state).state.machine.heap, memo⟩ events ∧ NoGlobal events := by
  refine ⟨(execute emptyGuard conjoin fuel code state).2, ?_, execute_silent emptyGuard conjoin fuel code state⟩
  simpa only [execute_erase] using execute_runs emptyGuard conjoin fuel code state memo

end MicroCFTA.SourceNativeGlobalUnfold
