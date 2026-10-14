import MicroCFTA.SourceRecursiveIntersectionNativeConstructorCoverage
import MicroCFTA.SourceRecursiveIntersectionMaybeMuPendingPhase

/-!
# Exact callback phase behind a pending native constructor

The native blocked result derives its original optional-binder site and
complete pre-call coverage. Actual source equations then identify the
Depth, ordinary, or fresh-body callback that stopped. An incomplete final
cache hit after two successful probes is excluded.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- An actual native constructor block derives its precise source site, payload coverage, and pending callback phase. -/
theorem constructor_trace_phase [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (code remaining : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (valid : InternedConstructorTemplates.Valid state.machine.heap) (covered : Covered [] state.machine.heap)
    (blocked : execute emptyGuard conjoin fuel code state = .blocked (.constructor key) remaining after) :
    ∃ steps before pair body next heap, steps < fuel ∧
      Steps emptyGuard conjoin steps code state (.optionalBinder pair body next) before ∧
      remaining = .optionalBinder pair body next ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.machine.heap = .pending key heap ∧
      after = advance before {before.machine with heap := heap} ∧
      InternedConstructorTemplates.Valid before.machine.heap ∧ Covered [] before.machine.heap ∧
      Reference.intersection pair.1 pair.2 ∈ body.free ∧
      SourceRecursiveIntersectionMaybeMu.PendingPhase (.intersection pair.1 pair.2) body before.machine.heap key heap := by
  obtain ⟨steps, before, pair, body, next, heap, smaller, trace, original, constructed, final, beforeValid, beforeCovered⟩ :=
    constructor_trace_covered emptyGuard conjoin fuel code remaining state after key valid covered blocked
  have phase := SourceRecursiveIntersectionMaybeMu.maybeMu_pending_phase pair body before.machine.heap heap key beforeValid beforeCovered constructed
  exact ⟨steps, before, pair, body, next, heap, smaller, trace, original, constructed, final, beforeValid, beforeCovered, phase⟩

end MicroCFTA.SourceRecursiveIntersectionNative
