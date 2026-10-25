import MicroCFTA.InternedFreshOrdinaryProbeHeap
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Filtered probes through actual repaired stored substitution

Available replacement inputs retain the source context. Actual execution
therefore preserves both stored Mu probe filters at every complete or pending
outcome. Unfolding supplies its original Mu as the sole replacement.
-/
namespace MicroCFTA.SourceEqualityProbeUnfold
open InternedConstructorTemplates InternedProbeProvenance
open InternedFreshOrdinaryContext (Context)
open InternedFreshOrdinaryProbeHeap (Heap)
open InternedStoredSubstitution (Environment Replacements)

/-- Actual stored execution retains filtered probes from its available original and replacement inputs. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state [])
    (heap : Heap state) (available : Available state value) (replacements : Replacements state environment) :
    Heap (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state := by
  have inputs := InternedStoredSubstitution.inputs_available value environment state available replacements
  exact InternedFreshOrdinaryProbeHeap.build_heap _ _ state
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩ heap

/-- Actual outer unfolding preserves filtered Mu probes without a completed unfolding premise. -/
theorem unfold [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state []) (heap : Heap state) (available : Available state value) :
    Heap (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      apply execute body _ state context heap (available.children body (by simp [InternedProbeProvenance.children]))
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · cases found

end MicroCFTA.SourceEqualityProbeUnfold
