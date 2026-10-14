import MicroCFTA.SourceFreshOrdinaryColdTable
import MicroCFTA.MergedFreshOrdinaryExposureLanguage

/-!
# Exact guarded language of finite repaired cold tables

The final-cache replay of every row supplies its exact repaired epsilon
language. Declared children and structural induction on finite terms then
identify the complete finite table with that final-cache graph. Initial
source-cache language transport and physical product semantics remain separate.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdTableLanguage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts Language SymbolicGraphView
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported heap graph_rows row_child)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows)
open SourcePreparedSharedRows (reference encode interpretedEdge)

/-- Exact final-cache row replay identifies the guarded row of each canonical physical root. -/
theorem row_node [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (rows : Rows Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (replayed : ReplayedRows state rows)
    (value : Value Symbol Guard) (available : Available state value) (identity : Nat)
    (same : reference value = some identity) (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges)
    (symbol : Symbol) (children : List (Term Symbol)) :
    EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state meaning) value (.node symbol children) ↔
      ∃ edge ∈ edges, edge.entry.key.symbol = symbol ∧
        All₂ (EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state meaning)) edge.children children ∧
        meaning edge.entry.key.constraint (.node symbol children) = true := by
  obtain ⟨original, fuel, originalAvailable, originalRef, originalClosed, read⟩ := replayed identity edges present
  have first := SourcePreparedSharedRows.read_identity state semantic.1.normal.facts value available identity same
  have second := SourcePreparedSharedRows.read_identity state semantic.1.normal.facts original originalAvailable identity originalRef
  have equal := Option.some.inj (first.symm.trans second)
  subst original
  rw [(MergedFreshOrdinaryExposureLanguage.actual_exact fuel value state semantic covered available originalClosed edges state read).2 meaning]
  constructor
  · rintro ⟨edge, member, terms, shape, runs, guard⟩
    obtain ⟨label, rfl⟩ := Term.node.inj shape
    exact ⟨edge, member, label.symm, runs, guard⟩
  · rintro ⟨edge, member, label, runs, guard⟩
    exact ⟨edge, member, children, by rw [label], runs, guard⟩

/-- Exact stored row equations and declared children give the original physical guarded language. -/
theorem language_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (rows : Rows Symbol Guard) (meaning : Guard → Term Symbol → Bool) (replayed : ReplayedRows state rows)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows) (value : Value Symbol Guard)
    (available : Available state value) (closed : value.free = []) (supported : Supported rows value) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state meaning) value term := by
  have facts := semantic.1.normal.facts
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → value.free = [] → Supported rows value →
      (Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
        EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state meaning) value term)) generalizing value with
  | node symbol children ih =>
      cases same : reference value with
      | none =>
          have empty : value = .empty := by
            cases value <;> simp only [reference] at same <;> try contradiction
            rfl
          subst value
          exact iff_of_false (SourceInternedRows.empty_rejects (heap rows) meaning _)
            (MergedFreshOrdinaryGraph.empty_rejects state meaning _)
      | some identity =>
          obtain ⟨edges, present⟩ := supported identity same
          rw [Language.accepts_node_iff, graph_rows rows value identity same edges present meaning,
            row_node state semantic covered rows meaning replayed value available identity same edges present]
          constructor
          · rintro ⟨edge, member, label, runs, guard⟩
            obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
            have mapped := (all₂_map_iff _ encode original.children children).mp runs
            refine ⟨original, selected, label, ?_, guard⟩
            apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ mapped
            intro child childIn term termIn accepted
            have provenance := row_child state facts rows resident closedRows identity edges present original selected child childIn
            exact (ih term termIn child provenance.1 provenance.2.1 provenance.2.2).mp accepted
          · rintro ⟨edge, member, label, runs, guard⟩
            refine ⟨renameEdge encode (interpretedEdge meaning edge), List.mem_map.mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
            apply (all₂_map_iff _ encode edge.children children).mpr
            apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
            intro child childIn term termIn accepted
            have provenance := row_child state facts rows resident closedRows identity edges present edge member child childIn
            exact (ih term termIn child provenance.1 provenance.2.1 provenance.2.2).mpr accepted
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available closed supported
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available closed supported
      · exact tail term member value available closed supported


/-- An actual finite repaired trace gives exactly the final-cache physical guarded language. -/
theorem trace_language_final [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = []) (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph final meaning) value term := by
  have inputs : SourceColdSharedRows.Inputs state [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨finalSemantic, finalCovered, growth, history, _, resident⟩ := trace.correct semantic covered inputs noRows
  have replayed := trace.replayed semantic covered inputs (by intro identity edges absent; cases absent)
  have closedRows := trace.closed (by intro identity edges absent; cases absent)
  exact language_exact final finalSemantic finalCovered rows meaning replayed resident closedRows value
    (available.grows state final growth history) closed (trace.pending_done value List.mem_cons_self) term

/-- Actual ascending finite-table readback has the exact final-cache repaired guarded language. -/
theorem trace_table_language_final [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning (SourceColdSharedRows.table rows keys value)))
      (encode value) term ↔ EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph final meaning) value term := by
  cases same : reference value with
  | none =>
      have empty : value = .empty := by
        cases value <;> simp only [reference] at same <;> try contradiction
        rfl
      subst value
      constructor
      · intro accepted
        cases accepted with
        | node edge children member runs guard =>
            simp [SourceColdSharedRows.table, reference, SourceInternedRows.interpretedRows, FTAValidation.rowFor,
              encode, SourceInternedRows.stateOf] at member
      · exact False.elim ∘ MergedFreshOrdinaryGraph.empty_rejects final meaning term
  | some identity =>
      simp only [SourceColdSharedRows.table, same]
      rw [SourceColdSharedRows.table_graph rows keys domain meaning]
      exact trace_language_final state final value rows trace semantic covered available closed meaning term

/-- Every closed source-derived cache supplies a finite stable table with exact final-cache guarded language. -/
theorem cold_table_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heapInvariant : InternedOpenDepthReadback.Heap state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ rows final outer inner, Trace state (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state (fun _ => none) [value] = .done rows final) ∧
      ∀ meaning term, Language.Accepts
        (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
          (SourceColdSharedRows.table rows (SourceFreshOrdinaryColdSharedRows.keys final rows) value))) (encode value) term ↔
        EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph final meaning) value term := by
  obtain ⟨rows, final, outer, inner, trace, _, _, _, _, _, _, _, _, _, domain, stable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table state semantic covered heapInvariant value available closed
  exact ⟨rows, final, outer, inner, trace, stable, fun meaning term =>
    trace_table_language_final state final value rows trace semantic covered available closed _ domain meaning term⟩

end MicroCFTA.SourceFreshOrdinaryColdTableLanguage
