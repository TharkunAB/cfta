import MicroCFTA.InternedGuardedExecution
import MicroCFTA.InternedGuardedStoredPlan
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Independent guarded meaning of actual repaired stored execution

The actual source execution theorem composes with the exact stored compiler.
Simultaneous substitution reads the original replacement languages. Outer Mu
unfolding returns the same independent language and retains the semantic heap.
-/
namespace MicroCFTA.InternedGuardedStoredExecution
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryContext InternedGuardedLanguage InternedGuardedProbeHeap InternedGuardedRequest
open InternedGuardedStoredPlan
open InternedNestedConstruction (Outcome)

/-- Available stored inputs establish the complete context for their exact compiled plan. -/
theorem plan_context (value : Value Symbol Guard) (replacements : Environment Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (available : Available state value) (valid : Replacements state replacements) :
    Context state ((leaves value).map (input replacements)) :=
  ⟨context.normal, InternedStoredSubstitution.inputs_available value replacements state available valid,
    context.profiles, context.freeNames⟩

/-- Actual simultaneous stored substitution has the independent replacement language and preserves its semantic heap. -/
theorem execute_checked [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (replacements : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state [])
    (heap : Heap state) (available : Available state value) (valid : Replacements state replacements) :
    Checked (InternedFreshOrdinaryStoredSubstitution.execute value replacements state) (fun result => ∀ holds ambient,
      meaning holds ambient result = meaning holds (replacementEnv holds ambient replacements) value) := by
  have built := InternedGuardedExecution.build_language (encode (leaves value) [] value) ((leaves value).map (input replacements))
    state (plan_context value replacements state context available valid) heap
  refine ⟨built.heap, ?_⟩
  intro result after done holds ambient
  have observed := built.result result after done holds ambient
  simp only [List.map_map, Function.comp_def] at observed
  exact observed.trans (execute_plan_language holds ambient value replacements state context.normal.facts.coherent available)

/-- Actual outer unfolding preserves independent meaning for arbitrary available stored records. -/
theorem unfold_checked [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state []) (heap : Heap state) (available : Available state value) :
    Checked (InternedFreshOrdinaryStoredSubstitution.unfold value state) (fun result => ∀ holds ambient,
      meaning holds ambient result = meaning holds ambient value) := by
  cases value with
  | empty | reference | node | union => exact done_checked _ _ _ heap (by intro holds ambient; rfl)
  | mu entry body depth ordinary =>
      have bodyAvailable := available.children body (by simp [children])
      let replacements : Environment Symbol Guard := fun name =>
        if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
      have valid : Replacements state replacements := by
        intro name replacement found
        dsimp only [replacements] at found
        split at found
        · cases found; exact available
        · contradiction
      have executed := execute_checked body replacements state context heap bodyAvailable valid
      refine ⟨executed.heap, ?_⟩
      intro result after done holds ambient
      exact ((executed.result result after done holds ambient).trans
        (execute_plan_language holds ambient body replacements state context.normal.facts.coherent bodyAvailable).symm).trans
        (unfold_plan_language holds ambient entry body depth ordinary state context.normal.facts.coherent bodyAvailable)

end MicroCFTA.InternedGuardedStoredExecution
