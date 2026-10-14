import MicroCFTA.SourceFreshOrdinaryColdTableLanguage
import MicroCFTA.SourceFreshOrdinaryColdGuardedHeap
import MicroCFTA.MergedFreshOrdinaryGuardedSoundness

/-!
# Final cold tables are sound for independent guarded meaning

Actual row replay supplies sound constructor languages. Declared children
and induction on finite terms give table and final-graph soundness. This
direction does not infer completeness from unfolding equations.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdGuardedSoundness
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedGuardedLanguage
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported heap graph_rows row_child)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows)
open SourcePreparedSharedRows (reference encode interpretedEdge)
open SymbolicGraphView

/-- A canonical available row root replays the exact source read stored for its identity. -/
theorem row_replay [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows) (value : Value Symbol Guard)
    (available : Available state value) (identity : Nat) (same : reference value = some identity)
    (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges) :
    ∃ fuel, MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges state := by
  obtain ⟨original, fuel, originalAvailable, originalRef, _, read⟩ := replayed identity edges present
  have first := SourcePreparedSharedRows.read_identity state facts value available identity same
  have second := SourcePreparedSharedRows.read_identity state facts original originalAvailable identity originalRef
  have equal := Option.some.inj (first.symm.trans second)
  subst original
  exact ⟨fuel, read⟩

/-- Each actual replayed row edge has only independently accepted terms of its canonical root. -/
theorem row_sound [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (replayed : ReplayedRows state rows) (value : Value Symbol Guard) (available : Available state value)
    (closed : value.free = []) (identity : Nat) (same : reference value = some identity)
    (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (term : Term Symbol)
    (accepted : edgeMeaning holds ambient edge term) : meaning holds ambient value term := by
  obtain ⟨fuel, read⟩ := row_replay state semantic.1.normal.facts rows replayed value available identity same edges present
  exact MergedFreshOrdinaryGuardedSoundness.nodeEdges_sound holds ambient fuel value state semantic covered guarded available closed
    edges state read edge member term accepted

/-- Every finite accepted table term belongs to the independent language of its physical root. -/
theorem language_sound [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (replayed : ReplayedRows state rows)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows) (value : Value Symbol Guard)
    (available : Available state value) (closed : value.free = []) (supported : Supported rows value) (term : Term Symbol)
    (accepted : Language.Accepts (SourceInternedRows.graph (heap rows) holds) (encode value) term) :
    meaning holds ambient value term := by
  have facts := semantic.1.normal.facts
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → value.free = [] → Supported rows value →
      Language.Accepts (SourceInternedRows.graph (heap rows) holds) (encode value) term → meaning holds ambient value term)
    generalizing value with
  | node symbol children ih =>
      cases same : reference value with
      | none =>
          have empty : value = .empty := by
            cases value <;> simp only [reference] at same <;> first | contradiction | rfl
          subst value
          exact False.elim (SourceInternedRows.empty_rejects (heap rows) holds _ accepted)
      | some identity =>
          obtain ⟨edges, present⟩ := supported identity same
          rw [Language.accepts_node_iff, graph_rows rows value identity same edges present holds] at accepted
          obtain ⟨edge, member, label, runs, guard⟩ := accepted
          obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
          have mapped := (all₂_map_iff _ encode original.children children).mp runs
          apply row_sound state semantic covered guarded rows replayed value available closed identity same edges present
            holds ambient original selected (.node symbol children)
          apply (edgeMeaning_all holds ambient original _).mpr
          refine ⟨children, ?_, ?_, guard⟩
          · change Term.node symbol children = Term.node original.entry.key.symbol children
            change original.entry.key.symbol = symbol at label
            rw [label]
          · apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ mapped
            intro child childIn term termIn accepted
            have provenance := row_child state facts rows resident closedRows identity edges present original selected child childIn
            exact ih term termIn child provenance.1 provenance.2.1 provenance.2.2 accepted
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available closed supported accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available closed supported accepted
      · exact tail term member value available closed supported accepted

/-- The actual repaired graph in a fully replayed final table is sound for independent meaning. -/
theorem graph_sound [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (replayed : ReplayedRows state rows)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows) (value : Value Symbol Guard)
    (available : Available state value) (closed : value.free = []) (supported : Supported rows value) (term : Term Symbol)
    (accepted : EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state holds) value term) : meaning holds ambient value term := by
  apply language_sound state semantic covered guarded rows holds ambient replayed resident closedRows value available closed supported term
  exact (SourceFreshOrdinaryColdTableLanguage.language_exact state semantic covered rows holds replayed resident closedRows value
    available closed supported term).mpr accepted

/-- An actual final shared graph accepts only independently accepted terms of the original root. -/
theorem trace_graph_sound [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (available : Available state value) (closed : value.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (term : Term Symbol)
    (accepted : EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph final holds) value term) : meaning holds ambient value term := by
  have inputs : SourceColdSharedRows.Inputs state [value] := by
    intro child member; simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨finalSemantic, finalCovered, growth, history, _, resident⟩ := trace.correct semantic covered inputs noRows
  have replayed := trace.replayed semantic covered inputs (by intro identity edges absent; cases absent)
  have closedRows := trace.closed (by intro identity edges absent; cases absent)
  exact graph_sound final finalSemantic finalCovered (trace.guarded_heap semantic covered guarded inputs) rows holds ambient
    replayed resident closedRows value (available.grows state final growth history) closed
    (trace.pending_done value List.mem_cons_self) term accepted

/-- The actual ascending final table is sound for the root's independent guarded language. -/
theorem trace_table_sound [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (available : Available state value) (closed : value.free = [])
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (term : Term Symbol)
    (accepted : Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds
      (SourceColdSharedRows.table rows keys value))) (encode value) term) : meaning holds ambient value term :=
  trace_graph_sound state final value rows trace semantic covered guarded available closed holds ambient term
    ((SourceFreshOrdinaryColdTableLanguage.trace_table_language_final state final value rows trace semantic covered available closed
      keys domain holds term).mp accepted)

end MicroCFTA.SourceFreshOrdinaryColdGuardedSoundness
