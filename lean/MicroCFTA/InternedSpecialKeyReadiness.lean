import MicroCFTA.InternedProfileReferenceInputs
import MicroCFTA.InternedNestedPreparedSites

/-!
# Complete special keys at actual syntax sites

A completed depth-body trace contains every nested binder site. Its
complete payload remains available after later cache effects. Readiness
tracks only the two smart-empty keys that are allowed to remain pending.
-/
namespace MicroCFTA.InternedSpecialKeyReadiness
open Cache InternedConstructorTemplates InternedNestedConstruction InternedNestedSpecialization
open InternedNestedTraceSites InternedNestedPreparedSites InternedProfileTraceSites
open InternedSpecialProbeKeys InternedProbeProvenance InternedNestedProvenance
open InternedStoredMuOrigins InternedNestedMissReadback InternedRootProfile
open InternedBinderProtocol (Reference NodeKey)

/-- A pending allowance already has every classified descendant payload. -/
def Ready (waiting : List NodeKey) (expression : Syntax Symbol Guard) (scope : Nat)
    (state : State Symbol Guard) : Prop :=
  ∀ smart body crossed, Site expression (.binder smart body) crossed →
    ∀ names : List Reference, names.length = scope + crossed →
    ∀ uses, key uses ∈ waiting → Classified body (names.map (fun name => some [name])) uses →
    ∃ record, state.nodeRecords (key uses) = some record

/-- Empty pending allowances impose no completed-site premise. -/
theorem ready_nil (expression : Syntax Symbol Guard) (scope : Nat) (state : State Symbol Guard) : Ready [] expression scope state := by
  intro smart body crossed site names length uses member classified
  cases member

/-- Later constructor effects retain each prepared recursive payload. -/
theorem Ready.grows (ready : Ready waiting expression scope before) (growth : Grows before after) :
    Ready waiting expression scope after := by
  intro smart body crossed site names length uses member classified
  obtain ⟨record, present⟩ := ready smart body crossed site names length uses member classified
  exact ⟨record, growth.nodeRecords _ record present⟩

/-- A descendant uses the exact count of crossed lexical binders. -/
theorem Ready.descendant (ready : Ready waiting expression scope state)
    (site : Site expression target crossed) : Ready waiting target (scope + crossed) state := by
  intro smart body inner nested names length uses member classified
  exact ready smart body (crossed + inner) (InternedNestedPreparedSites.Site.trans site nested)
    names (by simpa only [Nat.add_assoc] using length) uses member classified

/-- Both complete source probes preserve the profile context of their captured inputs. -/
theorem Context.callback [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (body : Syntax Symbol Guard) (name : Reference) (argument : Available state (.reference name)) :
    Context (callback body environment name state).state environment := by
  have all : Values state (.reference name :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact context.inputs value member
  have verified := callback_verified body environment name state context.normal.facts all
  exact ⟨callback_normal body environment name state context.normal all,
    fun value member => verified.available value (context.inputs value member),
    (InternedSourceProbeTags.callback_profile body environment name state context.normal all context.heap).heap⟩

/-- Source literal inputs have the corresponding literal root profiles. -/
theorem reference_profiles (names : List Reference) :
    (names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile = names.map (fun name => some [name]) := by
  simp only [List.map_map, Function.comp_def, profile]

/-- A completed trace prepares its actual descendant sites for every equal-length reference environment. -/
theorem ready_from_trace [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (names : List Reference)
    (before final after : State Symbol Guard) (value : Value Symbol Guard)
    (context : Context before (names.map Value.reference))
    (completed : build expression (names.map Value.reference) before = .done value final)
    (growth : Grows final after) (waiting : List NodeKey) : Ready waiting expression names.length after := by
  intro smart body crossed site other length uses member classified
  obtain ⟨start, result, finish, built, siteContext, _, suffix⟩ :=
    completed_site_checked site (names.map Value.reference) before value final context completed
  let inputs := List.replicate crossed Reference.depth ++ names
  have actual : inputs.map (Value.reference (Symbol := Symbol) (Guard := Guard)) =
      List.replicate crossed (.reference .depth) ++ names.map Value.reference := by
    simp [inputs]
  have sameClass : Classified body ((inputs.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map profile) uses := by
    rw [reference_profiles]
    exact (InternedProfileReferenceInputs.classified_equal_length body other inputs (by simp [inputs, length, Nat.add_comm]) uses).mp classified
  have actualClass : Classified body
      ((List.replicate crossed (Value.reference (Symbol := Symbol) (Guard := Guard) .depth) ++ names.map Value.reference).map profile) uses := by
    simpa only [actual] using sameClass
  obtain ⟨record, present⟩ := build_complete smart body _ start finish siteContext result built uses actualClass
  exact ⟨record, (grows_trans suffix growth).nodeRecords _ record present⟩

end MicroCFTA.InternedSpecialKeyReadiness
