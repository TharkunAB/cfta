import MicroCFTA.SourceRecursiveIntersectionNativeSemantic
import MicroCFTA.SourceRecursiveIntersectionNativeConstructorSplit
import MicroCFTA.SourceRecursiveIntersectionNativeConstructorCoverage

/-!
# Actual native source execution has no pending constructor

The proof follows finite source prefixes. A blocked appended body supplies
its own shorter blocked run or an actual completed body and continuation.
Completed bodies retain the semantic heaps. Exact optional-binder sites
therefore satisfy repaired source completion.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A range-checked actual source run from complete semantic heaps cannot report an unfinished constructor. -/
theorem no_constructor [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) {A : Type}
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (key : NodeKey) (remaining : Code Symbol Guard A) (post : Machine Symbol Guard → A → Prop)
    (clean : BodyCode code) (safe : Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (semantic : Semantic code state.machine) (heap : SemanticHeap state.machine.heap)
    (covered : Covered [] state.machine.heap) (ranges : WordRanges emptyGuard conjoin code state) :
    execute emptyGuard conjoin fuel code state ≠ .blocked (.constructor key) remaining after := by
  induction fuel using Nat.strongRecOn generalizing A code state after remaining with
  | ind fuel ih =>
    intro blocked
    cases fuel with
    | zero => cases blocked
    | succ fuel =>
      cases code with
      | pure | fail => cases blocked
      | work job next =>
          let actual := InternedConstructorTemplates.run job state.machine.heap
          let current : Machine Symbol Guard := {state.machine with heap := actual.2}
          have tail : execute emptyGuard conjoin fuel (next actual.1) (advance state current) = .blocked (.constructor key) remaining after := by
            simpa only [execute, step] using blocked
          exact ih fuel (by omega) _ _ _ _ post (clean actual.1) (safe.2.2 actual.1 current rfl)
            (advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1)
            (semantic.2 actual.1 current rfl) (semantic.1 heap)
            (InternedNestedCoverage.run_covered job state.machine.heap valid.machine.1.coherent.valid covered)
            (ranges.after_step emptyGuard conjoin _ _ _ _ rfl) tail
      | enter domain left right first second next =>
          let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
          let current : Machine Symbol Guard := {state.machine with domains := actual.2}
          have tail : execute emptyGuard conjoin fuel (next actual.1) (advance state current) = .blocked (.constructor key) remaining after := by
            simpa only [execute, step] using blocked
          exact ih fuel (by omega) _ _ _ _ post (clean actual.1) safe.2.2
            (advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1) semantic heap covered
            (ranges.after_step emptyGuard conjoin _ _ _ _ rfl) tail
      | read name next =>
          have tail : execute emptyGuard conjoin fuel (next (SourcePreparedSharedRows.read state.machine.heap name)) state =
              .blocked (.constructor key) remaining after := by simpa only [execute, step] using blocked
          exact ih fuel (by omega) _ _ _ _ post (clean _) safe valid semantic heap covered
            (ranges.after_step emptyGuard conjoin _ _ _ _ rfl) tail
      | optionalBinder pair body next =>
          cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap with
          | pending pending final =>
              exact False.elim (SourceRecursiveIntersectionMaybeMu.not_pending pair body state.machine.heap heap.1 semantic.1 heap.2
                covered pending final constructed)
          | done value final =>
              let current : Machine Symbol Guard := {state.machine with heap := final}
              have currentValid : SourceRecursiveIntersectionKernel.Valid current := by simpa only [constructed, construction, Result.state] using safe.1
              have physical : Extension state.machine current := by simpa only [constructed, construction, Result.state] using safe.2.1
              have actual : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap) state.machine = .done value current := by
                simp only [constructed, construction]; rfl
              have one : step emptyGuard conjoin (.optionalBinder pair body next) state = .yielded (next value) (advance state current) := by
                simp only [step, constructed]; rfl
              have tail : execute emptyGuard conjoin fuel (next value) (advance state current) = .blocked (.constructor key) remaining after := by
                simpa only [execute, one] using blocked
              have retained := SourceRecursiveIntersectionSemanticHeap.optionalBinder pair body state.machine.heap heap semantic.1
              have currentHeap : SemanticHeap final := by simpa only [constructed, InternedNestedConstruction.Outcome.state] using retained
              exact ih fuel (by omega) _ _ _ _ post (clean value) (safe.2.2 value current actual)
                (advance_valid width emptyGuard conjoin state valid current currentValid physical)
                (semantic.2 value current actual) currentHeap
                (SourceRecursiveIntersectionMaybeMu.maybeMu_covered pair body state.machine.heap valid.machine.1.coherent.valid covered value final constructed)
                (ranges.after_step emptyGuard conjoin _ _ _ _ one) tail
      | node request next =>
          cases lookup : lookupNode width request state with
          | mk selection chosen =>
            cases selection with
            | direct original =>
                obtain ⟨same, retained⟩ := lookupNode_direct request original state chosen lookup
                subst original
                subst chosen
                have one : step emptyGuard conjoin (.node request next) state = .yielded ((compileNode request).bind next) state := by
                  simp only [step, lookup]
                have tail : execute emptyGuard conjoin fuel ((compileNode request).bind next) state = .blocked (.constructor key) remaining after := by
                  simpa only [execute, one] using blocked
                have bodySafe := compileNode_safe request state.machine valid.machine safe.1
                exact ih fuel (by omega) _ _ _ _ post (bodyCode_bind _ _ (compileNode_bodyCode request) clean)
                  (safe_bind _ _ state.machine valid.machine (fun after value => Available after.heap value) post bodySafe
                    (fun value after afterValid physical available => safe.2 value after afterValid physical available)) valid
                  (semantic_bind _ _ state.machine valid.machine (fun after value => Available after.heap value) bodySafe
                    (compileNode_semantic request state.machine valid.machine semantic.1)
                    (fun value after afterValid physical available => semantic.2 value after afterValid physical available))
                  heap covered (ranges.after_step emptyGuard conjoin _ _ _ _ one) tail
            | memoized handle =>
                obtain ⟨requested, requestedKey, _, _⟩ := lookupNode_memoized request state chosen handle lookup
                have safeWord := ranges.current emptyGuard conjoin _ _ requested requestedKey
                cases demand : demandNode handle chosen with
                | mk observation current =>
                  cases observation with
                  | absent | busy => simp only [execute, step, lookup, demand] at blocked; cases blocked
                  | ready value =>
                      have called := node_ready_source emptyGuard conjoin state chosen current valid request safe.1 safeWord handle value lookup demand
                      have physical : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
                      have one : step emptyGuard conjoin (.node request next) state = .yielded (next value) current := by simp only [step, lookup, demand]
                      have tail : execute emptyGuard conjoin fuel (next value) current = .blocked (.constructor key) remaining after := by
                        simpa only [execute, one] using blocked
                      have currentHeap : SemanticHeap current.machine.heap := by rw [called.2.1]; exact heap
                      have currentCovered : Covered [] current.machine.heap := by rw [called.2.1]; exact covered
                      exact ih fuel (by omega) _ _ _ _ post (clean value)
                        (safe.2 value current.machine called.1.machine physical called.2.2.1) called.1
                        (semantic.2 value current.machine called.1.machine physical called.2.2.1) currentHeap currentCovered
                        (ranges.after_step emptyGuard conjoin _ _ _ _ one) tail
                  | evaluate original =>
                      have started := node_started_source emptyGuard conjoin state chosen current valid request original safe.1 safeWord handle lookup demand
                      have same := started.2.1
                      subst original
                      have ready : NodeReady current.machine request := by rw [started.2.2.1]; exact safe.1
                      have currentHeap : SemanticHeap current.machine.heap := by rw [started.2.2.1]; exact heap
                      have currentCovered : Covered [] current.machine.heap := by rw [started.2.2.1]; exact covered
                      have one : step emptyGuard conjoin (.node request next) state =
                          .yielded ((compileNode request).bind fun value => .finishNode handle value (next value)) current := by
                        simp only [step, lookup, demand]
                      have tail : execute emptyGuard conjoin fuel ((compileNode request).bind fun value => .finishNode handle value (next value)) current =
                          .blocked (.constructor key) remaining after := by simpa only [execute, one] using blocked
                      have entered := ranges.after_step emptyGuard conjoin _ _ _ _ one
                      have bodyRanges := entered.before_bind emptyGuard conjoin _ _ _
                      rcases constructor_bind_cases emptyGuard conjoin fuel (compileNode request) _ current after key remaining tail with
                        ⟨inner, rest, smaller, pending, same⟩ | ⟨inner, outer, value, middle, smaller, trace, pending⟩
                      · exact ih inner (by omega) _ _ _ _ (fun after value => Available after.heap value) (compileNode_bodyCode request)
                          (compileNode_safe request current.machine started.1.machine ready) started.1
                          (compileNode_semantic request current.machine started.1.machine ready) currentHeap currentCovered bodyRanges pending
                      · have evaluated := evaluation_of_trace emptyGuard conjoin inner (compileNode request) current middle value trace
                        have bounds := evaluated.bounds_of_ranges bodyRanges
                        have finished := Bounds.nodeStarted lookup demand safeWord bounds (Bounds.pure value _)
                        have completed := finished.correct (fun after value => Available after.heap value)
                          (by intro value; trivial) (safe_requestNode request.domain request.left request.right state.machine safe.1) valid
                        have bodyHeap := bounds.semantic_heap (fun after value => Available after.heap value) (compileNode_bodyCode request)
                          (compileNode_safe request current.machine started.1.machine ready) started.1
                          (compileNode_semantic request current.machine started.1.machine ready) currentHeap
                        have coverage := trace.covered emptyGuard conjoin inner _ _ current middle started.1.machine.1.coherent.valid currentCovered
                        have atFrame := entered.after_body emptyGuard conjoin _ _ _ _ value evaluated
                        cases outer with
                        | zero => cases pending
                        | succ outer =>
                            have tail : execute emptyGuard conjoin outer (next value) (SourceRecursiveIntersectionThunks.finishNode handle value middle) =
                                .blocked (.constructor key) remaining after := by simpa only [execute, step] using pending
                            exact ih outer (by omega) _ _ _ _ post (clean value)
                              (safe.2 value _ completed.valid.machine completed.growth completed.result) completed.valid
                              (semantic.2 value _ completed.valid.machine completed.growth completed.result) bodyHeap coverage.2
                              (atFrame.after_step emptyGuard conjoin _ _ _ _ rfl) tail
      | edge request next =>
          cases lookup : lookupEdge width request state with
          | mk handle chosen =>
            cases demand : demandEdge handle chosen with
            | mk observation current =>
              cases observation with
              | absent | busy => simp only [execute, step, lookup, demand] at blocked; cases blocked
              | ready value =>
                  have safeWord := ranges.current emptyGuard conjoin _ _
                  have called := edge_ready_source emptyGuard conjoin state chosen current valid request safe.1 safeWord handle value lookup demand
                  have physical : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
                  have one : step emptyGuard conjoin (.edge request next) state = .yielded (next value) current := by simp only [step, lookup, demand]
                  have tail : execute emptyGuard conjoin fuel (next value) current = .blocked (.constructor key) remaining after := by
                    simpa only [execute, one] using blocked
                  have currentHeap : SemanticHeap current.machine.heap := by rw [called.2.1]; exact heap
                  have currentCovered : Covered [] current.machine.heap := by rw [called.2.1]; exact covered
                  exact ih fuel (by omega) _ _ _ _ post (clean value)
                    (safe.2 value current.machine called.1.machine physical called.2.2.1) called.1
                    (semantic.2 value current.machine called.1.machine physical called.2.2.1) currentHeap currentCovered
                    (ranges.after_step emptyGuard conjoin _ _ _ _ one) tail
              | evaluate original =>
                  have safeWord := ranges.current emptyGuard conjoin _ _
                  have started := edge_started_source emptyGuard conjoin state chosen current valid request original safe.1 safeWord handle lookup demand
                  have same := started.2.1
                  subst original
                  have ready : EdgeReady current.machine request := by rw [started.2.2.1]; exact safe.1
                  have currentHeap : SemanticHeap current.machine.heap := by rw [started.2.2.1]; exact heap
                  have currentCovered : Covered [] current.machine.heap := by rw [started.2.2.1]; exact covered
                  have one : step emptyGuard conjoin (.edge request next) state =
                      .yielded ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge handle value (next value)) current := by
                    simp only [step, lookup, demand]
                  have tail : execute emptyGuard conjoin fuel ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge handle value (next value)) current =
                      .blocked (.constructor key) remaining after := by simpa only [execute, one] using blocked
                  have entered := ranges.after_step emptyGuard conjoin _ _ _ _ one
                  have bodyRanges := entered.before_bind emptyGuard conjoin _ _ _
                  rcases constructor_bind_cases emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) _ current after key remaining tail with
                    ⟨inner, rest, smaller, pending, same⟩ | ⟨inner, outer, value, middle, smaller, trace, pending⟩
                  · exact ih inner (by omega) _ _ _ _ (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
                      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
                      (compileEdge_semantic emptyGuard conjoin request current.machine started.1.machine ready) currentHeap currentCovered bodyRanges pending
                  · have evaluated := evaluation_of_trace emptyGuard conjoin inner (compileEdge emptyGuard conjoin request) current middle value trace
                    have bounds := evaluated.bounds_of_ranges bodyRanges
                    have finished := Bounds.edgeStarted lookup demand safeWord bounds (Bounds.pure value _)
                    have completed := finished.correct (fun after value => EdgeResident after.heap value)
                      (by intro value; trivial) (safe_requestEdge request.domain request.left request.right state.machine safe.1) valid
                    have bodyHeap := bounds.semantic_heap (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
                      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
                      (compileEdge_semantic emptyGuard conjoin request current.machine started.1.machine ready) currentHeap
                    have coverage := trace.covered emptyGuard conjoin inner _ _ current middle started.1.machine.1.coherent.valid currentCovered
                    have atFrame := entered.after_body emptyGuard conjoin _ _ _ _ value evaluated
                    cases outer with
                    | zero => cases pending
                    | succ outer =>
                        have tail : execute emptyGuard conjoin outer (next value) (SourceRecursiveIntersectionThunks.finishEdge handle value middle) =
                            .blocked (.constructor key) remaining after := by simpa only [execute, step] using pending
                        exact ih outer (by omega) _ _ _ _ post (clean value)
                          (safe.2 value _ completed.valid.machine completed.growth completed.result) completed.valid
                          (semantic.2 value _ completed.valid.machine completed.growth completed.result) bodyHeap coverage.2
                          (atFrame.after_step emptyGuard conjoin _ _ _ _ rfl) tail
      | finishNode | finishEdge => cases clean

end MicroCFTA.SourceRecursiveIntersectionNative
