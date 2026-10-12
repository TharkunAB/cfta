import MicroCFTA.InternedNestedErasureReplay

/-!
# Ordinary residual effects for unchanged results after dependency erasure

Residual work retains the exact extra source effects. Its result equals
the earlier completed result. Sequencing composes these locally derived
facts through actual earlier source traces.
-/
namespace MicroCFTA.InternedErasureResidual
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedErasureReplay InternedNestedSpecialization
open InternedErasedEdgeReplay (run_coherent)

/-- A later execution has certified ordinary effects and returns the exact earlier complete value. -/
def Residual [DecidableEq (EdgeKey Symbol Guard)] (value : Result) (final : State Symbol Guard)
    (execute : State Symbol Guard → Outcome Symbol Guard Result) : Prop :=
  ∃ code : Work Symbol Guard Result, Safe code ∧ Ordinary code ∧
    ∀ after, Coherent after → Grows final after → execute after = work code after ∧ (run code after).1 = value

/-- Exact replay needs no new constructor effect. -/
theorem pure_residual [DecidableEq (EdgeKey Symbol Guard)] (value : Result) (final : State Symbol Guard)
    (execute : State Symbol Guard → Outcome Symbol Guard Result)
    (replay : ∀ after, Coherent after → Grows final after → execute after = .done value after) :
    Residual value final execute := by
  refine ⟨.pure value, trivial, trivial, ?_⟩
  intro after coherent growth
  exact ⟨replay after coherent growth, rfl⟩

/-- An earlier complete finite constructor reuses its actual record and state after growth. -/
theorem work_residual [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (before final : State Symbol Guard) (value : Result) (valid : InternedConstructorTemplates.Valid before)
    (completed : work computation before = .done value final) : Residual value final (work computation) :=
  pure_residual value final (work computation) (fun after _ growth => work_replays computation before after value final valid completed growth)

/-- Derived residuals compose in the original source order and retain the earlier intermediate value. -/
theorem bind_residual [DecidableEq (EdgeKey Symbol Guard)] (first : State Symbol Guard → Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (head : First) (middle : State Symbol Guard) (value : Result) (final : State Symbol Guard)
    (firstResidual : Residual head middle first) (nextResidual : Residual value final (next head))
    (later : Grows middle final) : Residual value final (fun state => (first state).bind next) := by
  obtain ⟨firstCode, firstSafe, firstOrdinary, firstReplay⟩ := firstResidual
  obtain ⟨nextCode, nextSafe, nextOrdinary, nextReplay⟩ := nextResidual
  refine ⟨firstCode.bind (fun _ => nextCode), safe_bind _ _ firstSafe (fun _ => nextSafe),
    ordinary_bind _ _ firstOrdinary (fun _ => nextOrdinary), ?_⟩
  intro after coherent growth
  have firstDone := firstReplay after coherent (grows_trans later growth)
  let middleAfter := (run firstCode after).2
  have middleCoherent := run_coherent firstCode after firstSafe coherent
  have middleGrowth := (InternedConstructorTemplates.run_correct firstCode after coherent.valid).2
  have nextDone := nextReplay middleAfter middleCoherent (grows_trans growth middleGrowth)
  constructor
  · dsimp only
    rw [firstDone.1]
    simp only [work, Outcome.bind, run_bind]
    rw [firstDone.2]
    simpa only [work] using nextDone.1
  · simpa only [run_bind] using nextDone.2

end MicroCFTA.InternedErasureResidual
