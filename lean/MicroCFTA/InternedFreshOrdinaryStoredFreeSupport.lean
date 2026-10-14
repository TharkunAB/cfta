import MicroCFTA.InternedStoredPlanFreeSupport
import MicroCFTA.InternedStoredLeafShape
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Actual repaired substitution free-name support

Each returned free name comes from the replacement of an original free
reference. Closed captures supply no free name. Local source binders
exclude their own references from the captured lexical positions.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available leaves_available)
open InternedFreshOrdinaryContext InternedFreeNameIndexedOrigins
open InternedBinderProtocol (Reference)

/-- Every returned free name comes from an actual replacement of an original free reference. -/
theorem free_support [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state captures)
    (available : Available state body) (replacements : Replacements state environment)
    (value : Value Symbol Guard) (after : State Symbol Guard) (done : execute body environment state = .done value after)
    (name : Reference) (member : name ∈ value.free) :
    ∃ original, original ∈ body.free ∧ name ∈ ((environment original).getD (.reference original)).free := by
  have inputs := inputs_available body environment state available replacements
  have inputContext : Context state ((leaves body).map (input environment)) :=
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩
  obtain ⟨index, selected, used, found, named⟩ := source_indexed _ _ state inputContext value after done name member
  cases originalFound : (leaves body)[index]? with
  | none => simp [List.getElem?_map, originalFound] at found
  | some original =>
      have same : input environment original = selected := by simpa only [List.getElem?_map, originalFound, Option.map_some, Option.some.injEq] using found
      rw [← same] at named
      rcases InternedStoredLeafShape.leaves_shape body original (List.mem_of_getElem? originalFound) with closed | ⟨reference, rfl⟩
      · rw [InternedStoredSubstitutionScope.input_closed original environment closed, closed] at named
        cases named
      · have source := InternedStoredPlanFreeSupport.encode_free (leaves body) [] body state context.normal.facts.coherent
          (leaves_available body state available) available (fun _ member => member) index (.reference reference) originalFound reference
          (by simp [Value.free]) (by simpa only [List.length_nil, Nat.zero_add] using used)
        exact ⟨reference, source.1, named⟩

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution
