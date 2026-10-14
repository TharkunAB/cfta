import MicroCFTA.SourceRecursiveIntersectionNativeBodyProgress

/-!
# Finite row observations from smaller compiled bodies

Actual row lookup and demand select the original ordered request. Published
handles cannot be absent or busy under the strict active bound. The actual
body derives guarded row provenance. Its original frame restores the
caller's bound before it runs the retained continuation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- A row instruction has a finite terminal observation when smaller bodies and its actual continuation do. -/
theorem edge_terminal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (bodies : BodiesBelow source holds bound width emptyGuard conjoin)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : EdgeReady state.machine request)
    (below : EdgeBelow source holds bound request) (growth : Grows source state.machine.heap)
    (history : Extends source.nodes.issued state.machine.heap.nodes.issued) (active : ActiveAbove (view source holds) holds bound state)
    (ranges : WordRanges emptyGuard conjoin (.edge request next) state)
    (later : ∀ value after, SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after → Extension state.machine after.machine →
      EdgeResident after.machine.heap value → ActiveAbove (view source holds) holds bound after → WordRanges emptyGuard conjoin (next value) after →
      ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (next value) after)) :
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (.edge request next) state) := by
  obtain ⟨scope, complete, smaller⟩ := below
  let limit := requiredFuel (view source holds) (edgeSemantic holds request) complete
  have safeWord := ranges.current emptyGuard conjoin _ _
  cases lookup : lookupEdge width request state with
  | mk handle chosen =>
    have chosenActive : ActiveAbove (view source holds) holds bound chosen := by
      simpa only [lookup] using active.lookupEdge _ holds bound state request
    cases demand : demandEdge handle chosen with
    | mk observation current =>
      cases observation with
      | absent => exact False.elim (edge_absent_impossible state chosen current (shape_of_valid emptyGuard conjoin state valid) request handle lookup demand)
      | busy => exact False.elim (edge_busy_impossible (view source holds) holds bound emptyGuard conjoin state chosen current valid active
          request ready safeWord complete smaller handle lookup demand)
      | ready value =>
        have called := edge_ready_source emptyGuard conjoin state chosen current valid request ready safeWord handle value lookup demand
        have one : step emptyGuard conjoin (.edge request next) state = .yielded (next value) current := by simp only [step, lookup, demand]
        have physical : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
        have returnedActive : ActiveAbove (view source holds) holds bound current := by
          rw [(demandEdge_ready handle chosen current value demand).choose_spec.2]
          exact chosenActive
        exact returns_after_step emptyGuard conjoin _ _ _ _ one
          (later value current called.1 physical called.2.2.1 returnedActive (ranges.after_step emptyGuard conjoin _ _ _ _ one))
      | evaluate original =>
        have started := edge_started_source emptyGuard conjoin state chosen current valid request original ready safeWord handle lookup demand
        have same := started.2.1
        subst original
        have currentReady : EdgeReady current.machine request := by rw [started.2.2.1]; exact ready
        have currentGrowth : Grows source current.machine.heap := by rw [started.2.2.1]; exact growth
        have currentHistory : Extends source.nodes.issued current.machine.heap.nodes.issued := by rw [started.2.2.1]; exact history
        have currentActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) chosen).startEdge
          (view source holds) holds limit chosen current handle request demand complete (Nat.le_refl _)
        have one : step emptyGuard conjoin (.edge request next) state =
            .yielded ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge handle value (next value)) current := by
          simp only [step, lookup, demand]
        have entered := ranges.after_step emptyGuard conjoin _ _ _ _ one
        have bodyRanges := entered.before_bind emptyGuard conjoin _ _ _
        have observed := bodies.edges request scope complete smaller current started.1 currentReady currentGrowth currentHistory currentActive bodyRanges
        apply returns_after_step emptyGuard conjoin _ _ _ _ one
        apply returns_bind emptyGuard conjoin (compileEdge emptyGuard conjoin request) (fun value => .finishEdge handle value (next value)) current observed
        intro fuel value middle done
        have evaluated := evaluation_of_done emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) current middle value done
        have built := (evaluated.bounds_of_ranges bodyRanges).correct (fun after value => EdgeResident after.heap value)
          (compileEdge_bodyCode emptyGuard conjoin request) (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine currentReady) started.1
        obtain ⟨kernelFuel, repeated⟩ := built.meaning.edge_body
        have kernelDone : SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
            (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin kernelFuel request.domain) request.left request.right current.machine = .done value middle.machine := by
          simpa only [Nat.add_zero] using repeated 0
        have produced := SourceRecursiveIntersectionEdgeMemo.produced_here emptyGuard conjoin kernelFuel request.domain request.left request.right
          current.machine middle.machine started.1.machine currentReady.1 currentReady.2.1 currentReady.2.2 value kernelDone
        have cells := edge_body_cell emptyGuard conjoin handle request current middle value
          (shape_of_valid emptyGuard conjoin current started.1) started.2.2.2 evaluated
        have completed := finishEdge_valid width emptyGuard conjoin middle built.valid handle request value cells.1 produced
        have physical : Extension state.machine middle.machine := by rw [← started.2.2.1]; exact built.growth
        have restored := chosenActive.finishEdge (view source holds) holds bound emptyGuard conjoin handle request chosen current middle value
          demand (shape_of_valid emptyGuard conjoin current started.1) evaluated
        have atFrame := entered.after_body emptyGuard conjoin _ _ _ _ value evaluated
        have finishStep : step emptyGuard conjoin (.finishEdge handle value (next value)) middle =
            .yielded (next value) (SourceRecursiveIntersectionThunks.finishEdge handle value middle) := rfl
        exact returns_after_step emptyGuard conjoin _ _ _ _ finishStep
          (later value _ completed physical built.result restored (atFrame.after_step emptyGuard conjoin _ _ _ _ finishStep))

end MicroCFTA.SourceRecursiveIntersectionNative
