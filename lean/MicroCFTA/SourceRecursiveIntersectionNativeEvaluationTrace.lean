import MicroCFTA.SourceRecursiveIntersectionNativeCompletion

/-!
# Execute nested native evaluations

Each finite evaluation tree constructs an actual native trace with the same
result and complete caches. Together with extraction from completed runs,
the nested evaluation is exact operational evidence, not a supplied source
completion contract.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Every finite nested evaluation constructs its actual completed native trace. -/
theorem Evaluation.trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) :
    ∃ fuel, Steps emptyGuard conjoin fuel code state (.pure value) after := by
  induction evaluated with
  | pure => exact ⟨0, .refl _ _⟩
  | work tail ih | enter tail ih | read tail ih | finishNode tail ih | finishEdge tail ih =>
    obtain ⟨fuel, trace⟩ := ih
    exact ⟨fuel + 1, .cons _ _ _ _ _ _ _ rfl trace⟩
  | optionalBinder done tail ih =>
    obtain ⟨fuel, trace⟩ := ih
    refine ⟨fuel + 1, .cons _ _ _ _ _ _ _ ?_ trace⟩
    simp only [step, done]
  | @nodeDirect A request actual next state selected middle final value result lookup body tail bodyIH tailIH =>
    obtain ⟨inner, bodyTrace⟩ := bodyIH
    obtain ⟨outer, tailTrace⟩ := tailIH
    refine ⟨inner + outer + 1, .cons _ _ ((compileNode actual).bind next) selected _ _ _ ?_ ?_⟩
    · simp only [step, lookup]
    · apply Steps.trans emptyGuard conjoin inner outer
      case later => exact tailTrace
      case earlier => exact Steps.bind emptyGuard conjoin inner _ _ _ _ bodyTrace _
  | nodeReady lookup demand tail ih | edgeReady lookup demand tail ih =>
    obtain ⟨fuel, trace⟩ := ih
    refine ⟨fuel + 1, .cons _ _ _ _ _ _ _ ?_ trace⟩
    simp only [step, lookup, demand]
  | @nodeStarted A request actual next state selected current middle final handle value result lookup demand body tail bodyIH tailIH =>
    obtain ⟨inner, bodyTrace⟩ := bodyIH
    obtain ⟨outer, tailTrace⟩ := tailIH
    refine ⟨inner + (outer + 1) + 1, .cons _ _
      ((compileNode actual).bind fun value => .finishNode handle value (next value)) current _ _ _ ?_ ?_⟩
    · simp only [step, lookup, demand]
    · apply Steps.trans emptyGuard conjoin inner (outer + 1)
      · exact Steps.bind emptyGuard conjoin inner _ _ _ _ bodyTrace (fun value => .finishNode handle value (next value))
      · exact .cons _ _ _ _ _ _ _ rfl tailTrace
  | @edgeStarted A request actual next state selected current middle final handle value result lookup demand body tail bodyIH tailIH =>
    obtain ⟨inner, bodyTrace⟩ := bodyIH
    obtain ⟨outer, tailTrace⟩ := tailIH
    refine ⟨inner + (outer + 1) + 1, .cons _ _
      ((compileEdge emptyGuard conjoin actual).bind fun value => .finishEdge handle value (next value)) current _ _ _ ?_ ?_⟩
    · simp only [step, lookup, demand]
    · apply Steps.trans emptyGuard conjoin inner (outer + 1)
      · exact Steps.bind emptyGuard conjoin inner _ _ _ _ bodyTrace (fun value => .finishEdge handle value (next value))
      · exact .cons _ _ _ _ _ _ _ rfl tailTrace

/-- Every finite nested evaluation supplies a sufficient native bound for its exact result. -/
theorem Evaluation.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) :
    ∃ fuel, execute emptyGuard conjoin fuel code state = .done value after := by
  obtain ⟨fuel, trace⟩ := evaluated.trace
  exact ⟨fuel + 1, trace_done emptyGuard conjoin fuel code state after value trace⟩

/-- Nested evaluation and actual finite completed native execution agree in both directions. -/
theorem completed_iff_evaluation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A) :
    (∃ fuel, execute emptyGuard conjoin fuel code state = .done value after) ↔
      Evaluation width Symbol Guard emptyGuard conjoin code state value after := by
  constructor
  · rintro ⟨fuel, done⟩
    exact evaluation_of_done emptyGuard conjoin fuel code state after value done
  · intro evaluated
    exact evaluated.done

end MicroCFTA.SourceRecursiveIntersectionNative
