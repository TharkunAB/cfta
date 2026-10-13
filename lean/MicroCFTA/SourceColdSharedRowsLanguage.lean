import MicroCFTA.SourceColdSharedRowsMeaning
import MicroCFTA.SourcePreparedSharedRowsLanguage

/-!
# Exact language of the stateful cold traversal output

The output map supplies the graph. Completed traversal declares every
nonempty child. Actual final-cache row equations and finite-term induction
give exactly the original physical language, without a warmup premise.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency MergedPhysicalWarmup
open Language SymbolicGraphView
open SourcePreparedSharedRows (reference encode exposure interpretedEdge)

/-- The actual completed map supplies every exposed shared row. -/
def heap (rows : Rows Symbol Guard) : SourceInternedRows.Heap Symbol Guard :=
  fun identity => ((rows identity).getD []).map exposure

/-- A nonempty physical root has an actual row in the completed map. -/
def Supported (rows : Rows Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ identity, reference value = some identity → ∃ edges, rows identity = some edges

/-- A copied graph row retains its exact source order and complete annotations. -/
theorem graph_rows (rows : Rows Symbol Guard) (value : Value Symbol Guard) (identity : Nat)
    (same : reference value = some identity) (edges : List (EdgeValue Symbol Guard))
    (present : rows identity = some edges) (meaning : Guard → Term Symbol → Bool) :
    SourceInternedRows.graph (heap rows) meaning (encode value) =
      edges.map (fun edge => renameEdge encode (interpretedEdge meaning edge)) := by
  simp only [encode, same, SourceInternedRows.stateOf, SourceInternedRows.graph, heap, present,
    Option.getD_some, List.map_map]
  apply List.map_congr_left
  intro edge _
  simp only [Function.comp_apply, SourceInternedRows.interpret, SourceInternedRows.transition,
    exposure, renameEdge, interpretedEdge, List.map_map]
  rfl

/-- Canonical physical readback identifies a final row's original root exactly. -/
theorem row_node [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (rows : Rows Symbol Guard) (meaning : Guard → Term Symbol → Bool) (correct : MeaningRows state rows meaning)
    (value : Value Symbol Guard) (available : Available state value) (identity : Nat)
    (same : reference value = some identity) (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges)
    (symbol : Symbol) (children : List (Term Symbol)) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value (.node symbol children) ↔
      ∃ edge ∈ edges, edge.entry.key.symbol = symbol ∧
        All₂ (EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning)) edge.children children ∧
        meaning edge.entry.key.constraint (.node symbol children) = true := by
  obtain ⟨original, originalAvailable, originalRef, _, _, exactRows⟩ := correct identity edges present
  have first := SourcePreparedSharedRows.read_identity state facts value available identity same
  have second := SourcePreparedSharedRows.read_identity state facts original originalAvailable identity originalRef
  have equal := Option.some.inj (first.symm.trans second)
  subst original
  rw [exactRows]
  constructor
  · rintro ⟨edge, member, terms, shape, runs, guard⟩
    obtain ⟨label, rfl⟩ := Term.node.inj shape
    exact ⟨edge, member, label.symm, runs, guard⟩
  · rintro ⟨edge, member, label, runs, guard⟩
    exact ⟨edge, member, children, by rw [label], runs, guard⟩

/-- Every stored edge child retains its closed physical provenance and output declaration. -/
theorem row_child (state : State Symbol Guard) (facts : Facts state) (rows : Rows Symbol Guard)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows) (identity : Nat)
    (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard) (inside : child ∈ edge.children) :
    Available state child ∧ child.free = [] ∧ Supported rows child := by
  obtain ⟨_, _, _, _, edgesResident, childrenClosed⟩ := resident identity edges present
  exact ⟨facts.cached.edges edge.entry.key edge (edgesResident edge member) child inside,
    childrenClosed edge member child inside, closedRows identity edges present edge member child inside⟩

/-- Exact stored row equations and declared children give the original physical guarded language. -/
theorem language_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (rows : Rows Symbol Guard) (meaning : Guard → Term Symbol → Bool) (correct : MeaningRows state rows meaning)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows) (value : Value Symbol Guard)
    (available : Available state value) (closed : value.free = []) (supported : Supported rows value) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → value.free = [] → Supported rows value →
      (Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term)) generalizing value with
  | node symbol children ih =>
      cases same : reference value with
      | none =>
          have empty : value = .empty := by
            cases value <;> simp only [reference] at same <;> try contradiction
            rfl
          subst value
          exact iff_of_false (SourceInternedRows.empty_rejects (heap rows) meaning _)
            (MergedPhysicalUnion.empty_rejects state meaning _)
      | some identity =>
          obtain ⟨edges, present⟩ := supported identity same
          rw [Language.accepts_node_iff, graph_rows rows value identity same edges present meaning,
            row_node state facts rows meaning correct value available identity same edges present]
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

/-- The output of a completed actual cold walk has exactly its initial root's physical language. -/
theorem Trace.language_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap rows) meaning) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term := by
  have inputs : Inputs state [value] := by
    intro child member
    rw [List.mem_singleton.mp member]
    exact ⟨available, closed⟩
  have initialRows : ResidentRows state (fun _ => none) := by intro _ _ impossible; cases impossible
  obtain ⟨finalFacts, _, growth, history, _, _, resident⟩ := trace.correct facts prepared inputs initialRows
  have correct := trace.meaning facts prepared inputs meaning (by intro _ _ impossible; cases impossible)
  have closedRows := trace.closed (by intro _ _ impossible; cases impossible)
  have supported : Supported rows value := trace.pending_done value List.mem_cons_self
  exact (SourceColdSharedRows.language_exact final finalFacts rows meaning correct resident closedRows value
    (available.grows state final growth history) closed supported term).trans
    (MergedColdGraphTransport.accepts_stable state final facts finalFacts prepared growth history meaning value available term).symm

end MicroCFTA.SourceColdSharedRows
