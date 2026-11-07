import MicroCFTA.SourceSynthesisUniverseStoredRows
import MicroCFTA.InternedNodeSetCongruence

/-!
# Actual edge replay after canonical source-row ordering

Canonical ordering retains every complete resident source row.
The actual edge requests therefore retain the same target row set.
The final node request has the same normalized rows and cache effects.
No equality of source and target sort orders is required.
-/
namespace MicroCFTA.SourceSynthesisUniverseCanonicalRowReplay
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedStoredSubstitution
open InternedBinderProtocol (Reference NodeKey)

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem map_aligned {A B : Type} (relation : A → B → Prop) (f : A → B) (values : List A)
    (related : ∀ value ∈ values, relation value (f value)) :
    All₂ relation values (values.map f) := by
  induction values with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (related first List.mem_cons_self)
        (ih (fun value member => related value (List.mem_cons_of_mem _ member)))

private theorem replay_outputs (top : Guard) (environment : Environment Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard)
    (sources targets : List (EdgeValue Symbol Guard))
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        (target, current)) sources targets) :
    targets = sources.map (fun source =>
      (run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current).1) ∧
    ∀ source ∈ sources,
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        ((run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current).1,
          current) := by
  induction replayed with
  | nil => exact ⟨rfl, by intro source member; cases member⟩
  | @cons source target sources targets own rest ih =>
      have head := congrArg Prod.fst own
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, head, ih.1]
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · rw [own]
        · exact ih.2 selected later

/-- Canonical source order preserves actual replay and the complete target row set. -/
theorem canonical_replay (top : Guard) (environment : Environment Symbol Guard)
    (sources targets : List (EdgeValue Symbol Guard))
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (sourceResident : ∀ source ∈ sources, EdgeResident current source)
    (targetResident : ∀ target ∈ targets, EdgeResident current target)
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        (target, current)) sources targets) :
    ∃ canonicalTargets,
      All₂ (fun source target =>
        run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
          (target, current)) (canonicalEdges sources) canonicalTargets ∧
      (∀ row, row ∈ canonicalTargets ↔ row ∈ targets) ∧
      (∀ row ∈ canonicalTargets, EdgeResident current row) ∧
      makeNode canonicalTargets = makeNode targets := by
  let targetOf := fun source : EdgeValue Symbol Guard =>
    (run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current).1
  let canonicalTargets := (canonicalEdges sources).map targetOf
  have outputs := replay_outputs top environment current sources targets replayed
  have canonicalReplay : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        (target, current)) (canonicalEdges sources) canonicalTargets := by
    apply map_aligned
    intro source member
    exact outputs.2 source (canonicalEdges_member sources source member)
  have members : ∀ row, row ∈ canonicalTargets ↔ row ∈ targets := by
    intro row
    constructor
    · intro member
      obtain ⟨source, included, same⟩ := List.mem_map.mp member
      rw [outputs.1]
      exact List.mem_map.mpr ⟨source, canonicalEdges_member sources source included, same⟩
    · intro member
      rw [outputs.1] at member
      obtain ⟨source, included, same⟩ := List.mem_map.mp member
      exact List.mem_map.mpr
        ⟨source, canonicalEdges_retains current facts.coherent sources source sourceResident included, same⟩
  have canonicalResident : ∀ row ∈ canonicalTargets, EdgeResident current row :=
    fun row member => targetResident row ((members row).mp member)
  refine ⟨canonicalTargets, canonicalReplay, members, canonicalResident, ?_⟩
  apply InternedNodeSetCongruence.makeNode_same_members current facts.coherent
    canonicalTargets targets canonicalResident targetResident
  intro row
  simp only [surviving, List.mem_filter, members row]

/-- The actual stored executor uses the same final node request as the raw target rows. -/
theorem execute_eq_work_of_raw (top : Guard) (name : Reference) (entry : Interned NodeKey)
    (sources targets : List (EdgeValue Symbol Guard)) (marker : Value Symbol Guard)
    (environment : Environment Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (available : Available current (.node entry (canonicalEdges sources) 0 [name]))
    (closed : marker.free = [])
    (sourceResident : ∀ source ∈ sources, EdgeResident current source)
    (targetResident : ∀ target ∈ targets, EdgeResident current target)
    (tops : ∀ source ∈ sources, source.entry.key.constraint = top)
    (kinds : ∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference name)
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        (target, current)) sources targets) :
    InternedFreshOrdinaryStoredSubstitution.execute (.node entry (canonicalEdges sources) 0 [name])
        environment current = InternedNestedConstruction.work (makeNode targets) current := by
  obtain ⟨canonicalTargets, canonicalReplay, _, _, same⟩ :=
    canonical_replay top environment sources targets current facts sourceResident targetResident replayed
  have done := SourceSynthesisUniverseStoredRows.execute_reference_eq_work top name entry
    (canonicalEdges sources) canonicalTargets marker environment current facts available closed
    (fun source member => tops source (canonicalEdges_member sources source member))
    (fun source member => kinds source (canonicalEdges_member sources source member)) canonicalReplay
  simpa only [same] using done

end MicroCFTA.SourceSynthesisUniverseCanonicalRowReplay
