import MicroCFTA.SourceRecursiveIntersectionNativeSourceCalls
import MicroCFTA.SourceRecursiveIntersectionNativeWordRanges
import MicroCFTA.SourceRecursiveIntersectionNativeBindLower
import MicroCFTA.SourceRecursiveIntersectionNativePrimitiveLower
import MicroCFTA.SourceRecursiveIntersectionNativePrefixCoverage

/-!
# Actual native request prefixes from compiled-body bounds

The body supplier is an intermediate induction hypothesis.
The concrete branch induction must discharge it.
Lookup, demand, and memo completion retain the constructor heap.
The conclusions cover every finite native outcome.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedStoredPlanBinderDepthProgress

/-- Every actual node-request prefix inherits the bound of its compiled body. -/
theorem node_prefix_from_body
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (ranges : WordRanges emptyGuard conjoin (.node request .pure) state) (bound : Nat)
    (bodyLower : ∀ current : SourceRecursiveIntersectionThunks.State width Symbol Guard,
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → current.machine = state.machine →
      WordRanges emptyGuard conjoin (compileNode request) current → ∀ fuel,
        Lower current.machine.heap bound (execute emptyGuard conjoin fuel (compileNode request) current).state.machine.heap)
    (fuel : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.node request .pure) state).state.machine.heap := by
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel =>
      cases lookup : lookupNode width request state with
      | mk selection chosen =>
          have chosenMachine : chosen.machine = state.machine := by
            simpa only [lookup] using lookupNode_machine request state
          cases selection with
          | direct actual =>
              obtain ⟨same, retained⟩ := lookupNode_direct request actual state chosen lookup
              subst actual
              subst chosen
              have entered : WordRanges emptyGuard conjoin ((compileNode request).bind .pure) state :=
                ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup])
              have bodyRanges := entered.before_bind emptyGuard conjoin (compileNode request) .pure state
              have lower := execute_bind_lower emptyGuard conjoin fuel (compileNode request) .pure state bound
                (bodyLower state valid rfl bodyRanges)
                (fun _ value current _ outer => pure_lower emptyGuard conjoin outer value current bound)
              simpa only [execute, step, lookup] using lower
          | memoized handle =>
              cases demand : demandNode handle chosen with
              | mk observation current =>
                  have currentMachine : current.machine = state.machine := by
                    have same : current.machine = chosen.machine := by
                      simpa only [demand] using demandNode_machine handle chosen
                    exact same.trans chosenMachine
                  cases observation with
                  | absent =>
                      simpa only [execute, step, lookup, demand, Outcome.state, currentMachine] using
                        lower_refl state.machine.heap bound
                  | busy =>
                      simpa only [execute, step, lookup, demand, Outcome.state, currentMachine] using
                        lower_refl state.machine.heap bound
                  | ready value =>
                      have lower := pure_lower emptyGuard conjoin fuel value current bound
                      simpa only [execute, step, lookup, demand, currentMachine] using lower
                  | evaluate actual =>
                      have words := ranges.current emptyGuard conjoin (.node request .pure) state
                      obtain ⟨key, requested, _published, _machine⟩ :=
                        lookupNode_memoized request state chosen handle lookup
                      have safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right :=
                        words key requested
                      have started := node_started_source emptyGuard conjoin state chosen current valid request actual
                        ready safe handle lookup demand
                      have same := started.2.1
                      subst actual
                      have entered : WordRanges emptyGuard conjoin
                          ((compileNode request).bind fun value => .finishNode handle value (.pure value)) current :=
                        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
                      have bodyRanges := entered.before_bind emptyGuard conjoin (compileNode request)
                        (fun value => .finishNode handle value (.pure value)) current
                      have lower := execute_bind_lower emptyGuard conjoin fuel (compileNode request)
                        (fun value => .finishNode handle value (.pure value)) current bound
                        (bodyLower current started.1 currentMachine bodyRanges)
                        (fun _ value after _ outer => finishNode_lower emptyGuard conjoin outer handle value after bound)
                      simpa only [execute, step, lookup, demand, currentMachine] using lower

/-- Every actual edge-request prefix inherits the bound of its compiled body. -/
theorem edge_prefix_from_body
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (ranges : WordRanges emptyGuard conjoin (.edge request .pure) state) (bound : Nat)
    (bodyLower : ∀ current : SourceRecursiveIntersectionThunks.State width Symbol Guard,
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → current.machine = state.machine →
      WordRanges emptyGuard conjoin (compileEdge emptyGuard conjoin request) current → ∀ fuel,
        Lower current.machine.heap bound
          (execute emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) current).state.machine.heap)
    (fuel : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.edge request .pure) state).state.machine.heap := by
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel =>
      cases lookup : lookupEdge width request state with
      | mk handle chosen =>
          have chosenMachine : chosen.machine = state.machine := by
            simpa only [lookup] using lookupEdge_machine request state
          cases demand : demandEdge handle chosen with
          | mk observation current =>
              have currentMachine : current.machine = state.machine := by
                have same : current.machine = chosen.machine := by
                  simpa only [demand] using demandEdge_machine handle chosen
                exact same.trans chosenMachine
              cases observation with
              | absent =>
                  simpa only [execute, step, lookup, demand, Outcome.state, currentMachine] using
                    lower_refl state.machine.heap bound
              | busy =>
                  simpa only [execute, step, lookup, demand, Outcome.state, currentMachine] using
                    lower_refl state.machine.heap bound
              | ready value =>
                  have lower := pure_lower emptyGuard conjoin fuel value current bound
                  simpa only [execute, step, lookup, demand, currentMachine] using lower
              | evaluate actual =>
                  have safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right :=
                    ranges.current emptyGuard conjoin (.edge request .pure) state
                  have started := edge_started_source emptyGuard conjoin state chosen current valid request actual
                    ready safe handle lookup demand
                  have same := started.2.1
                  subst actual
                  have entered : WordRanges emptyGuard conjoin
                      ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge handle value (.pure value)) current :=
                    ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
                  have bodyRanges := entered.before_bind emptyGuard conjoin (compileEdge emptyGuard conjoin request)
                    (fun value => .finishEdge handle value (.pure value)) current
                  have lower := execute_bind_lower emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request)
                    (fun value => .finishEdge handle value (.pure value)) current bound
                    (bodyLower current started.1 currentMachine bodyRanges)
                    (fun _ value after _ outer => finishEdge_lower emptyGuard conjoin outer handle value after bound)
                  simpa only [execute, step, lookup, demand, currentMachine] using lower

end MicroCFTA.SourceRecursiveIntersectionNative
