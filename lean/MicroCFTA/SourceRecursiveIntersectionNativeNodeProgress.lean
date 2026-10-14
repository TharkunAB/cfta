import MicroCFTA.SourceRecursiveIntersectionNativeBodyProgress

/-!
# Finite node observations from smaller compiled bodies

Actual lookup and demand select the original request. Published handles
cannot be absent or busy under the strict active bound. A completed body
derives its own provenance before its original frame stores the result.
The caller's active bound is then restored for its actual continuation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- A node instruction has a finite terminal observation when smaller bodies and its actual continuation do. -/
theorem node_terminal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (bodies : BodiesBelow source holds bound width emptyGuard conjoin)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : NodeReady state.machine request)
    (below : NodeBelow source holds bound request) (growth : Grows source state.machine.heap)
    (history : Extends source.nodes.issued state.machine.heap.nodes.issued) (active : ActiveAbove (view source holds) holds bound state)
    (ranges : WordRanges emptyGuard conjoin (.node request next) state)
    (later : ∀ value after, SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after → Extension state.machine after.machine →
      Available after.machine.heap value → ActiveAbove (view source holds) holds bound after → WordRanges emptyGuard conjoin (next value) after →
      ∃ fuel, Terminal (execute emptyGuard conjoin fuel (next value) after)) :
    ∃ fuel, Terminal (execute emptyGuard conjoin fuel (.node request next) state) := by
  obtain ⟨scope, complete, smaller⟩ := below
  let limit := requiredFuel (view source holds) (nodeSemantic request) complete
  cases lookup : lookupNode width request state with
  | mk selection chosen =>
    cases selection with
    | direct original =>
      obtain ⟨same, retained⟩ := lookupNode_direct request original state chosen lookup
      subst original
      subst chosen
      have one : step emptyGuard conjoin (.node request next) state = .yielded ((compileNode request).bind next) state := by
        simp only [step, lookup]
      have entered := ranges.after_step emptyGuard conjoin _ _ _ _ one
      have bodyRanges := entered.before_bind emptyGuard conjoin _ _ _
      have observed := bodies.nodes request scope complete smaller state valid ready growth history
        (active.weaken _ holds bound limit (Nat.le_of_lt smaller) state) bodyRanges
      apply terminal_after_step emptyGuard conjoin _ _ _ _ one
      apply terminal_bind emptyGuard conjoin (compileNode request) next state observed
      intro fuel value after done
      have evaluated := evaluation_of_done emptyGuard conjoin fuel (compileNode request) state after value done
      have built := (evaluated.bounds_of_ranges bodyRanges).correct (fun after value => Available after.heap value)
        (compileNode_bodyCode request) (compileNode_safe request state.machine valid.machine ready) valid
      have returnedActive := active.running_before _ holds bound state after
        (evaluated.running_before (compileNode_bodyCode request) (shape_of_valid emptyGuard conjoin state valid))
      exact later value after built.valid built.growth built.result returnedActive
        (entered.after_body emptyGuard conjoin _ _ _ _ value evaluated)
    | memoized handle =>
      obtain ⟨key, requested, _, _⟩ := lookupNode_memoized request state chosen handle lookup
      have safeWord := ranges.current emptyGuard conjoin _ _ key requested
      have chosenActive : ActiveAbove (view source holds) holds bound chosen := by
        simpa only [lookup] using active.lookupNode _ holds bound state request
      cases demand : demandNode handle chosen with
      | mk observation current =>
        cases observation with
        | absent => exact False.elim (node_absent_impossible state chosen current (shape_of_valid emptyGuard conjoin state valid) request handle lookup demand)
        | busy => exact False.elim (node_busy_impossible (view source holds) holds bound emptyGuard conjoin state chosen current valid active
            request ready safeWord complete smaller handle lookup demand)
        | ready value =>
          have called := node_ready_source emptyGuard conjoin state chosen current valid request ready safeWord handle value lookup demand
          have one : step emptyGuard conjoin (.node request next) state = .yielded (next value) current := by simp only [step, lookup, demand]
          have physical : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
          have returnedActive : ActiveAbove (view source holds) holds bound current := by
            rw [(demandNode_ready handle chosen current value demand).choose_spec.2]
            exact chosenActive
          exact terminal_after_step emptyGuard conjoin _ _ _ _ one
            (later value current called.1 physical called.2.2.1 returnedActive (ranges.after_step emptyGuard conjoin _ _ _ _ one))
        | evaluate original =>
          have started := node_started_source emptyGuard conjoin state chosen current valid request original ready safeWord handle lookup demand
          have same := started.2.1
          subst original
          have currentReady : NodeReady current.machine request := by rw [started.2.2.1]; exact ready
          have currentGrowth : Grows source current.machine.heap := by rw [started.2.2.1]; exact growth
          have currentHistory : Extends source.nodes.issued current.machine.heap.nodes.issued := by rw [started.2.2.1]; exact history
          have currentActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) chosen).startNode
            (view source holds) holds limit chosen current handle request demand complete (Nat.le_refl _)
          have one : step emptyGuard conjoin (.node request next) state =
              .yielded ((compileNode request).bind fun value => .finishNode handle value (next value)) current := by
            simp only [step, lookup, demand]
          have entered := ranges.after_step emptyGuard conjoin _ _ _ _ one
          have bodyRanges := entered.before_bind emptyGuard conjoin _ _ _
          have observed := bodies.nodes request scope complete smaller current started.1 currentReady currentGrowth currentHistory currentActive bodyRanges
          apply terminal_after_step emptyGuard conjoin _ _ _ _ one
          apply terminal_bind emptyGuard conjoin (compileNode request) (fun value => .finishNode handle value (next value)) current observed
          intro fuel value middle done
          have evaluated := evaluation_of_done emptyGuard conjoin fuel (compileNode request) current middle value done
          have built := (evaluated.bounds_of_ranges bodyRanges).correct (fun after value => Available after.heap value)
            (compileNode_bodyCode request) (compileNode_safe request current.machine started.1.machine currentReady) started.1
          obtain ⟨kernelFuel, repeated⟩ := built.meaning.node_body
          have kernelDone : SourceRecursiveIntersectionKernel.execute emptyGuard conjoin kernelFuel request.domain request.left request.right current.machine = .done value middle.machine := by
            simpa only [Nat.add_zero] using repeated 0
          have produced := SourceRecursiveIntersectionMemo.produced_here emptyGuard conjoin kernelFuel request.domain request.left request.right
            current.machine middle.machine started.1.machine currentReady.1 currentReady.2.1 currentReady.2.2 value kernelDone
          have cells := node_body_cell emptyGuard conjoin handle request current middle value
            (shape_of_valid emptyGuard conjoin current started.1) started.2.2.2 evaluated
          have completed := finishNode_valid width emptyGuard conjoin middle built.valid handle request value cells.1 produced
          have physical : Extension state.machine middle.machine := by rw [← started.2.2.1]; exact built.growth
          have restored := chosenActive.finishNode (view source holds) holds bound emptyGuard conjoin handle request chosen current middle value
            demand (shape_of_valid emptyGuard conjoin current started.1) evaluated
          have atFrame := entered.after_body emptyGuard conjoin _ _ _ _ value evaluated
          have finishStep : step emptyGuard conjoin (.finishNode handle value (next value)) middle =
              .yielded (next value) (SourceRecursiveIntersectionThunks.finishNode handle value middle) := rfl
          exact terminal_after_step emptyGuard conjoin _ _ _ _ finishStep
            (later value _ completed physical built.result restored (atFrame.after_step emptyGuard conjoin _ _ _ _ finishStep))

end MicroCFTA.SourceRecursiveIntersectionNative
