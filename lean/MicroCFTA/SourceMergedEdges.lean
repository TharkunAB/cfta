import MicroCFTA.SourceMergedColumns

/-!
# General successful small and large merge rows

Small rows keep their full symbol and guard. Large rows keep the common
symbol and use the source Top guard. All child results retain their actual
closed payloads and cover the original independent row languages.
-/
namespace MicroCFTA.SourceMergedEdges
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map small)
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)
open MergedPhysicalGroupEdges (SameKey columns_member makeEdge_fields)
open SourceMergedContracts SourceMergedColumns

/-- A successful small row retains its original symbol and guard after all actual child effects. -/
theorem small_done [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (law : RecurseLaw call holds ambient)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : EdgeResident before edge) (closed : ClosedValues edge.children) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) : Effect before after ∧ EdgePost holds ambient [edge] after result := by
  have facts := semantic.ready.semantic.1.normal.facts
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have checked := children_done call holds ambient law edge.children before semantic
    (facts.cached.edges edge.entry.key edge resident) closed values middle mapped
  have available : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.available))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.closed))
  have constructed := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle checked.1.2.ready available
  have fields := makeEdge_fields middle checked.1.2.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values available
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  refine ⟨checked.1.trans ⟨constructed.1, SourceEqualityRequiredSemanticCache.edge _ _ _ middle checked.1.2 available⟩,
    constructed.2.1, ?_, ?_⟩
  · rw [fields.2.2]; exact valuesClosed
  · intro original member term accepted
    rw [List.mem_singleton.mp member] at accepted
    obtain ⟨terms, same, runs, guard⟩ := accepted
    refine ⟨terms, ?_, ?_, ?_⟩
    · rw [fields.1]; exact same
    · rw [fields.2.2]
      exact covers_runs holds ambient (fun value => [value]) _ _ middle checked.2 terms
        (runs.imp (fun value term accepted => ⟨value, List.mem_cons_self, accepted⟩))
    · rw [fields.2.1]; exact guard

/-- A successful large row covers every original row through its actual merged columns. -/
theorem large_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (fuel : Nat) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (law : RecurseLaw call holds ambient)
    (top : Guard) (topTrue : ∀ term, holds top term = true)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) (keys : SameKey (first :: rest))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before (first :: rest))
    (closed : ClosedEdges (first :: rest)) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.large call clear fuel top first rest before = .done result after) :
    Effect before after ∧ EdgePost holds ambient (first :: rest) after result := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have checked := map_done (SourceMergedWorker.column call clear fuel)
    (fun state inputs => Values state inputs ∧ ClosedValues inputs) (fun state inputs result => ValuePost holds ambient inputs state result)
    (fun _ _ effects _ inputs => ⟨(fun value member => effects.1.available value (inputs.1 value member)), inputs.2⟩)
    (fun _ _ effects _ _ post => post.grows effects) columns
    (fun inputs _ state ready valid result final done => column_done call clear fuel holds ambient clearTrue law inputs state ready valid.1 valid.2 result final done)
    before semantic (fun column member => ⟨(by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner)⟩) values middle mapped
  have available : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.available))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.closed))
  have constructed := SourceEqualityRequiredCache.edge first.entry.key.symbol top values middle checked.1.2.ready available
  have fields := makeEdge_fields middle checked.1.2.ready.semantic.1.normal.facts first.entry.key.symbol top values available
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  refine ⟨checked.1.trans ⟨constructed.1, SourceEqualityRequiredSemanticCache.edge _ _ _ middle checked.1.2 available⟩,
    constructed.2.1, ?_, ?_⟩
  · rw [fields.2.2]; exact valuesClosed
  · intro edge member term accepted
    obtain ⟨terms, same, runs, guard⟩ := accepted
    have key := keys edge member first List.mem_cons_self
    refine ⟨terms, ?_, ?_, ?_⟩
    · rw [fields.1, ← key.1]; exact same
    · rw [fields.2.2]
      apply covers_runs holds ambient id columns values middle checked.2 terms
      have covered := MergedAlternativesGroups.columns_cover (meaning holds ambient) ((first :: rest).map EdgeValue.children)
        edge.children terms (List.mem_map.mpr ⟨edge, member, rfl⟩) runs
      simpa only [key.2, id, columns] using covered
    · rw [fields.2.1]; exact topTrue term

end MicroCFTA.SourceMergedEdges
