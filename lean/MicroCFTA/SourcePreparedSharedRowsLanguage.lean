import MicroCFTA.SourcePreparedSharedRows
import MicroCFTA.SourcePhysicalSharedRowsLanguage

/-!
# Exact guarded language of prepared shared rows

Each row comes from an actual stable source read. Induction on the finite
term transports its ordered child runs through canonical source identities.
This includes Mu and union roots, arbitrary guards, and cyclic references.
-/
namespace MicroCFTA.SourcePreparedSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedPhysicalMergeContext Language SymbolicGraphView

noncomputable section

/-- Interpret the complete source edge without changing its child records. -/
def interpretedEdge (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) :
    Language.Edge (Value Symbol Guard) Symbol := ⟨edge.entry.key.symbol, edge.children, meaning edge.entry.key.constraint⟩

/-- Exact source exposure describes the original physical node language. -/
theorem physical_node [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (meaning : Guard → Term Symbol → Bool) (symbol : Symbol) (children : List (Term Symbol)) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value (.node symbol children) ↔
      ∃ edge ∈ rows state outputs context prepared value, edge.entry.key.symbol = symbol ∧
        All₂ (EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning)) edge.children children ∧
        meaning edge.entry.key.constraint (.node symbol children) = true := by
  obtain ⟨fuel, done, _, _, _⟩ := rows_read state outputs context prepared value available closed
  rw [(MergedSourceExposureCoverage.actual_exact fuel value state context.facts prepared available _ state done).2]
  constructor
  · rintro ⟨edge, member, terms, same, runs, guard⟩
    obtain ⟨label, rfl⟩ := Term.node.inj same
    exact ⟨edge, member, label.symm, runs, guard⟩
  · rintro ⟨edge, member, label, runs, guard⟩
    exact ⟨edge, member, children, by rw [label], runs, guard⟩

/-- Empty records expose no rows. -/
theorem rows_empty [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state) :
    rows state outputs context prepared .empty = [] := by
  obtain ⟨fuel, done, _, _, _⟩ := rows_read state outputs context prepared .empty (empty_available state) rfl
  exact (MergedSourceExposure.Result.done.inj done).1.symm

/-- Actual shared rows copy every original source edge in its returned order. -/
theorem graph_rows [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (meaning : Guard → Term Symbol → Bool) :
    SourceInternedRows.graph (heap state outputs context prepared) meaning (encode value) =
      (rows state outputs context prepared value).map (fun edge => renameEdge encode (interpretedEdge meaning edge)) := by
  cases value with
  | empty => simp [encode, reference, SourceInternedRows.stateOf, SourceInternedRows.graph, rows_empty]
  | reference name => simp [Value.free] at closed
  | node entry edges depth free | union entry members depth free | mu entry body depth ordinary =>
      have found := read_identity state context.facts _ available entry.identity rfl
      simp only [encode, reference, SourceInternedRows.stateOf, SourceInternedRows.graph, heap, found,
        Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
      apply List.map_congr_left
      intro edge _
      simp only [Function.comp_apply, SourceInternedRows.interpret, SourceInternedRows.transition,
        exposure, renameEdge, interpretedEdge, List.map_map]
      rfl

/-- Prepared shared-row language equals the actual physical epsilon language. -/
theorem language_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap state outputs context prepared) meaning) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → value.free = [] →
      (Language.Accepts (SourceInternedRows.graph (heap state outputs context prepared) meaning) (encode value) term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term)) generalizing value with
  | node symbol children ih =>
      rw [Language.accepts_node_iff, graph_rows state outputs context prepared value available closed meaning,
        physical_node state outputs context prepared value available closed meaning]
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        have mapped := (all₂_map_iff _ encode original.children children).mp runs
        refine ⟨original, present, label, ?_, guard⟩
        apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ mapped
        intro child childIn term termIn accepted
        have provenance := rows_child state outputs context prepared value original present child childIn
        exact (ih term termIn child provenance.1 provenance.2).mp accepted
      · rintro ⟨edge, member, label, runs, guard⟩
        refine ⟨renameEdge encode (interpretedEdge meaning edge), List.mem_map.mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
        apply (all₂_map_iff _ encode edge.children children).mpr
        apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
        intro child childIn term termIn accepted
        have provenance := rows_child state outputs context prepared value edge member child childIn
        exact (ih term termIn child provenance.1 provenance.2).mpr accepted
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available closed
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available closed
      · exact tail term member value available closed

/-- The completed finite table has exactly the original physical guarded language. -/
theorem toRows_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (fuel : Nat) (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (done : SourceInternedRows.toRows (heap state outputs context prepared) fuel (reference value) = some raw)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term :=
  (SourceInternedRows.toRows_language _ meaning fuel (reference value) raw done term).trans
    (language_exact state outputs context prepared value available closed meaning term)

end
end MicroCFTA.SourcePreparedSharedRows
