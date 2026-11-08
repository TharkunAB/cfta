import MicroCFTA.InternedFreshOrdinaryProbeHeap
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion

set_option autoImplicit false
open scoped Classical

/-!
# Generic probe births in actual stored unfolding

Actual stored unfolding derives clean probes from its literal build.
This law does not depend on the current caller Context.
-/
namespace MicroCFTA.SourceCurrentConjunctionProbeBirth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)

/-- Actual stored unfolding retains old probes and derives clean probes for new binders. -/
theorem unfold_heap {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    {captures : List (Value Symbol Guard)} (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state captures)
    (probes : InternedFreshOrdinaryProbeHeap.Heap state) (available : Available state value) :
    InternedFreshOrdinaryProbeHeap.Heap
      (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact probes
  | mu entry body depth ordinary =>
    let environment : Environment Symbol Guard := fun name =>
      if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
    have replacements : Replacements state environment := by
      intro name replacement found
      dsimp only [environment] at found
      split at found
      · cases found
        exact available
      · cases found
    have inputs := inputs_available body environment state
      (available.children body (by simp [children])) replacements
    have sourceContext : InternedFreshOrdinaryContext.Context state ((leaves body).map (input environment)) :=
      ⟨context.normal, inputs, context.profiles, context.freeNames⟩
    exact InternedFreshOrdinaryProbeHeap.build_heap (encode (leaves body) [] body)
      ((leaves body).map (input environment)) state sourceContext probes

end MicroCFTA.SourceCurrentConjunctionProbeBirth
