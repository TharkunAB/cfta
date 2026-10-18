import MicroCFTA.SourceCurrentStoredPlanEquivalence

/-!
# Available lexical inputs for one stored Mu body

A local binding shadows the original replacement map at one name.
Unmapped names remain absent. Identity fallback is used only when a plan
reads that name. The encoded local body has the same complete outcome as
repaired execution with this partial replacement map.
-/
namespace MicroCFTA.SourceCurrentStoredMuLexicalInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

/-- The local value overrides its exact source name and retains all other mappings. -/
def shadow (self : Reference) (localValue : Value Symbol Guard)
    (environment : Environment Symbol Guard) : Environment Symbol Guard :=
  fun name => if name = self then some localValue else environment name

/-- Initial replacements and the available local value remain available after actual growth. -/
theorem replacements (self : Reference) (localValue : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before after : State Symbol Guard)
    (initial : Replacements before environment) (growth : Grows before after)
    (issued : Extends before.nodes.issued after.nodes.issued)
    (localAvailable : Available after localValue) :
    Replacements after (shadow self localValue environment) := by
  intro name value found
  by_cases same : name = self
  · have equal : localValue = value := by simpa only [shadow, same, ite_true, Option.some.injEq] using found
    exact equal ▸ localAvailable
  · have original : environment name = some value := by simpa only [shadow, same, ite_false] using found
    exact (initial name value original).grows before after growth issued

private theorem resolved (self name : Reference) (localValue : Value Symbol Guard)
    (environment : Environment Symbol Guard) :
    resolve [self] [localValue] environment name =
      (shadow self localValue environment name).getD (.reference name) := by
  rw [resolve_cons]
  by_cases same : self = name
  · subst name
    simp [shadow]
  · simp [resolve, shadow, same, Ne.symm same]

/-- The exact local encoded call equals repaired execution with the partial shadow map at any heap. -/
theorem build_shadow [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (body : Value Symbol Guard)
    (self : Reference) (localValue : Value Symbol Guard) (environment : Environment Symbol Guard)
    (source current : State Symbol Guard) (coherent : Coherent source)
    (contextAvailable : Values source context) (available : Available source body)
    (covered : ∀ leaf ∈ leaves body, leaf ∈ context) :
    InternedFreshOrdinaryConstruction.build (encode context [self] body)
      (localValue :: context.map (input environment)) current =
      InternedFreshOrdinaryStoredSubstitution.execute body (shadow self localValue environment) current := by
  have plans := SourceCurrentStoredPlanEquivalence.encode_equivalent context (leaves body) body
    [self] [] [localValue] [] environment (shadow self localValue environment) source coherent
    contextAvailable (leaves_available body source available) covered (fun _ member => member) rfl rfl (by
      intro name
      simpa only [resolve, List.findIdx?_nil] using resolved self name localValue environment)
  simpa only [List.cons_append, List.nil_append, InternedFreshOrdinaryStoredSubstitution.execute] using
    InternedFreshOrdinaryPlanEquivalence.build_exact _ _ _ _ current plans

end MicroCFTA.SourceCurrentStoredMuLexicalInputs
