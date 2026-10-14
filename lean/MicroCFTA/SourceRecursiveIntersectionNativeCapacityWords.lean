import MicroCFTA.SourceRecursiveIntersectionNativeCacheRanges
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate
import MicroCFTA.SourceRecursiveIntersectionCompileSafety

/-!
# Derived native word safety on all actual prefixes

Finite-prefix induction follows source effects and both native memo families.
Completed inner bodies derive their own checked correspondence before a memo
completion frame runs. Only actual cache capacity is supplied by the caller.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNativeCapacity
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionNative

/-- Every actual native source prefix has safe request words when its reached caches fit. -/
theorem prefix_words [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) {A : Type}
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (remaining : Code Symbol Guard A) (post : Machine Symbol Guard → A → Prop)
    (clean : BodyCode code) (safe : Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid (bits + 2) emptyGuard conjoin state)
    (ranges : CacheRanges bits emptyGuard conjoin code state)
    (trace : Steps emptyGuard conjoin fuel code state remaining after) : Words (bits + 2) remaining := by
  induction fuel using Nat.strongRecOn generalizing A code state after remaining with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          obtain ⟨same, retained⟩ := steps_zero emptyGuard conjoin _ _ _ _ trace
          subst remaining
          subst after
          exact words bits code state.machine valid.machine (ranges.current bits emptyGuard conjoin code state)
            (request_ready code state.machine post safe)
      | succ fuel =>
          obtain ⟨rest, current, first, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
          cases code with
          | pure | fail => cases first
          | finishNode | finishEdge => cases clean
          | work job next =>
              let actual := InternedConstructorTemplates.run job state.machine.heap
              let machine : Machine Symbol Guard := {state.machine with heap := actual.2}
              have one : step emptyGuard conjoin (.work job next) state = .yielded (next actual.1) (advance state machine) := rfl
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
              exact ih fuel (by omega) _ _ _ _ post (clean actual.1) (safe.2.2 actual.1 machine rfl)
                (advance_valid (bits + 2) emptyGuard conjoin state valid machine safe.1 safe.2.1)
                (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
          | enter domain left right leftKey rightKey next =>
              let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right leftKey rightKey
              let machine : Machine Symbol Guard := {state.machine with domains := actual.2}
              have one : step emptyGuard conjoin (.enter domain left right leftKey rightKey next) state =
                  .yielded (next actual.1) (advance state machine) := rfl
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
              exact ih fuel (by omega) _ _ _ _ post (clean actual.1) safe.2.2
                (advance_valid (bits + 2) emptyGuard conjoin state valid machine safe.1 safe.2.1)
                (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
          | read name next =>
              have one : step emptyGuard conjoin (.read name next) state =
                  .yielded (next (SourcePreparedSharedRows.read state.machine.heap name)) state := rfl
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
              exact ih fuel (by omega) _ _ _ _ post (clean _) safe valid
                (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
          | optionalBinder pair body next =>
              cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap with
              | pending key final => simp only [step, constructed] at first; cases first
              | done value final =>
                  let machine : Machine Symbol Guard := {state.machine with heap := final}
                  have machineValid : SourceRecursiveIntersectionKernel.Valid machine := by
                    simpa only [constructed, construction, Result.state] using safe.1
                  have physical : Extension state.machine machine := by
                    simpa only [constructed, construction, Result.state] using safe.2.1
                  have actual : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.machine.heap) state.machine =
                      .done value machine := by simp only [constructed, construction]; rfl
                  have one : step emptyGuard conjoin (.optionalBinder pair body next) state =
                      .yielded (next value) (advance state machine) := by simp only [step, constructed]; rfl
                  obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                  exact ih fuel (by omega) _ _ _ _ post (clean value) (safe.2.2 value machine actual)
                    (advance_valid (bits + 2) emptyGuard conjoin state valid machine machineValid physical)
                    (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
          | node request next =>
              cases lookup : lookupNode (bits + 2) request state with
              | mk selection chosen =>
                  cases selection with
                  | direct original =>
                      obtain ⟨same, retained⟩ := lookupNode_direct request original state chosen lookup
                      subst original
                      subst chosen
                      have one : step emptyGuard conjoin (.node request next) state = .yielded ((compileNode request).bind next) state := by
                        simp only [step, lookup]
                      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                      have bodySafe := compileNode_safe request state.machine valid.machine safe.1
                      exact ih fuel (by omega) _ _ _ _ post (bodyCode_bind _ _ (compileNode_bodyCode request) clean)
                        (safe_bind _ _ state.machine valid.machine (fun after value => Available after.heap value) post bodySafe
                          (fun value after afterValid physical available => safe.2 value after afterValid physical available)) valid
                        (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
                  | memoized handle =>
                      obtain ⟨requested, requestedKey, _, _⟩ := lookupNode_memoized request state chosen handle lookup
                      have safeWord := node_key_safe bits state.machine valid.machine (ranges.current bits emptyGuard conjoin _ _) request safe.1 requested requestedKey
                      cases demand : demandNode handle chosen with
                      | mk observation entered =>
                          cases observation with
                          | absent | busy => simp only [step, lookup, demand] at first; cases first
                          | ready value =>
                              have called := node_ready_source emptyGuard conjoin state chosen entered valid request safe.1 safeWord handle value lookup demand
                              have physical : Extension state.machine entered.machine := by rw [called.2.1]; exact .refl _
                              have one : step emptyGuard conjoin (.node request next) state = .yielded (next value) entered := by simp only [step, lookup, demand]
                              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                              exact ih fuel (by omega) _ _ _ _ post (clean value)
                                (safe.2 value entered.machine called.1.machine physical called.2.2.1) called.1
                                (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
                          | evaluate original =>
                              have started := node_started_source emptyGuard conjoin state chosen entered valid request original safe.1 safeWord handle lookup demand
                              have same := started.2.1
                              subst original
                              have ready : NodeReady entered.machine request := by rw [started.2.2.1]; exact safe.1
                              have bodySafe := compileNode_safe request entered.machine started.1.machine ready
                              have one : step emptyGuard conjoin (.node request next) state =
                                  .yielded ((compileNode request).bind fun value => .finishNode handle value (next value)) entered := by
                                simp only [step, lookup, demand]
                              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                              have enteredRanges := ranges.after_step bits emptyGuard conjoin _ _ _ _ one
                              have bodyCapacity := enteredRanges.before_bind bits emptyGuard conjoin _ _ _
                              rcases steps_bind_cases emptyGuard conjoin fuel (compileNode request) _ entered after remaining tail with
                                ⟨inner, bodyTrace, nonpure, same⟩ | ⟨inner, outer, value, middle, count, bodyTrace, outerTrace⟩
                              · rw [same]
                                exact words_bind_nonpure (bits + 2) inner _ nonpure
                                  (ih fuel (by omega) _ _ _ _ (fun after value => Available after.heap value)
                                    (compileNode_bodyCode request) bodySafe started.1 bodyCapacity bodyTrace)
                              · have bodyRanges := wordRanges_of_complete emptyGuard conjoin inner (compileNode request) entered middle value bodyTrace
                                  (fun extra next final shorter bodyPrefix => ih extra (by omega) _ _ _ _ (fun after value => Available after.heap value)
                                    (compileNode_bodyCode request) bodySafe started.1 bodyCapacity bodyPrefix)
                                have evaluated := evaluation_of_trace emptyGuard conjoin inner (compileNode request) entered middle value bodyTrace
                                have bounds := evaluated.bounds_of_ranges bodyRanges
                                have finished := Bounds.nodeStarted lookup demand safeWord bounds (Bounds.pure value _)
                                have completed := finished.correct (fun after value => Available after.heap value)
                                  (by intro value; trivial) (safe_requestNode request.domain request.left request.right state.machine safe.1) valid
                                have atFrame := enteredRanges.after_body bits emptyGuard conjoin _ _ _ _ inner value bodyTrace
                                cases outer with
                                | zero =>
                                    obtain ⟨same, _⟩ := steps_zero emptyGuard conjoin _ _ _ _ outerTrace
                                    rw [← same]
                                    trivial
                                | succ outer =>
                                    obtain ⟨rest, final, finish, later⟩ := steps_succ emptyGuard conjoin outer _ _ _ _ outerTrace
                                    obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj finish
                                    exact ih outer (by omega) _ _ _ _ post (clean value)
                                      (safe.2 value _ completed.valid.machine completed.growth completed.result) completed.valid
                                      (atFrame.after_step bits emptyGuard conjoin _ _ _ _ rfl) later
          | edge request next =>
              have safeWord := edge_key_safe bits state.machine valid.machine (ranges.current bits emptyGuard conjoin _ _) request safe.1
              cases lookup : lookupEdge (bits + 2) request state with
              | mk handle chosen =>
                  cases demand : demandEdge handle chosen with
                  | mk observation entered =>
                      cases observation with
                      | absent | busy => simp only [step, lookup, demand] at first; cases first
                      | ready value =>
                          have called := edge_ready_source emptyGuard conjoin state chosen entered valid request safe.1 safeWord handle value lookup demand
                          have physical : Extension state.machine entered.machine := by rw [called.2.1]; exact .refl _
                          have one : step emptyGuard conjoin (.edge request next) state = .yielded (next value) entered := by simp only [step, lookup, demand]
                          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                          exact ih fuel (by omega) _ _ _ _ post (clean value)
                            (safe.2 value entered.machine called.1.machine physical called.2.2.1) called.1
                            (ranges.after_step bits emptyGuard conjoin _ _ _ _ one) tail
                      | evaluate original =>
                          have started := edge_started_source emptyGuard conjoin state chosen entered valid request original safe.1 safeWord handle lookup demand
                          have same := started.2.1
                          subst original
                          have ready : EdgeReady entered.machine request := by rw [started.2.2.1]; exact safe.1
                          have bodySafe := compileEdge_safe emptyGuard conjoin request entered.machine started.1.machine ready
                          have one : step emptyGuard conjoin (.edge request next) state =
                              .yielded ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge handle value (next value)) entered := by
                            simp only [step, lookup, demand]
                          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
                          have enteredRanges := ranges.after_step bits emptyGuard conjoin _ _ _ _ one
                          have bodyCapacity := enteredRanges.before_bind bits emptyGuard conjoin _ _ _
                          rcases steps_bind_cases emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) _ entered after remaining tail with
                            ⟨inner, bodyTrace, nonpure, same⟩ | ⟨inner, outer, value, middle, count, bodyTrace, outerTrace⟩
                          · rw [same]
                            exact words_bind_nonpure (bits + 2) inner _ nonpure
                              (ih fuel (by omega) _ _ _ _ (fun after value => EdgeResident after.heap value)
                                (compileEdge_bodyCode emptyGuard conjoin request) bodySafe started.1 bodyCapacity bodyTrace)
                          · have bodyRanges := wordRanges_of_complete emptyGuard conjoin inner (compileEdge emptyGuard conjoin request) entered middle value bodyTrace
                              (fun extra next final shorter bodyPrefix => ih extra (by omega) _ _ _ _ (fun after value => EdgeResident after.heap value)
                                (compileEdge_bodyCode emptyGuard conjoin request) bodySafe started.1 bodyCapacity bodyPrefix)
                            have evaluated := evaluation_of_trace emptyGuard conjoin inner (compileEdge emptyGuard conjoin request) entered middle value bodyTrace
                            have bounds := evaluated.bounds_of_ranges bodyRanges
                            have finished := Bounds.edgeStarted lookup demand safeWord bounds (Bounds.pure value _)
                            have completed := finished.correct (fun after value => EdgeResident after.heap value)
                              (by intro value; trivial) (safe_requestEdge request.domain request.left request.right state.machine safe.1) valid
                            have atFrame := enteredRanges.after_body bits emptyGuard conjoin _ _ _ _ inner value bodyTrace
                            cases outer with
                            | zero =>
                                obtain ⟨same, _⟩ := steps_zero emptyGuard conjoin _ _ _ _ outerTrace
                                rw [← same]
                                trivial
                            | succ outer =>
                                obtain ⟨rest, final, finish, later⟩ := steps_succ emptyGuard conjoin outer _ _ _ _ outerTrace
                                obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj finish
                                exact ih outer (by omega) _ _ _ _ post (clean value)
                                  (safe.2 value _ completed.valid.machine completed.growth completed.result) completed.valid
                                  (atFrame.after_step bits emptyGuard conjoin _ _ _ _ rfl) later

/-- Actual cache-counter bounds derive every native request word check without supplied completion or provenance. -/
theorem wordRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (post : Machine Symbol Guard → A → Prop) (clean : BodyCode code) (safe : Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid (bits + 2) emptyGuard conjoin state)
    (ranges : CacheRanges bits emptyGuard conjoin code state) : WordRanges emptyGuard conjoin code state :=
  fun fuel remaining after trace => prefix_words bits emptyGuard conjoin fuel code state after remaining post clean safe valid ranges trace

end MicroCFTA.SourceRecursiveIntersectionNativeCapacity
