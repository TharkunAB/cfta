import MicroCFTA.SourceNativeBoundDepthMeaning
import MicroCFTA.SourcePreparedSharedRowsLanguage

/-!
# Full-guard rows of the current ordinary native component

The snapshot reads the current issued keys and immutable native payloads.
Only ordinary node records contribute rows. Full guards and row order remain.
The language theorem applies to the available recursively ordinary component.
The final heap can retain unrelated recursive records.
-/
namespace MicroCFTA.SourceNativeOrdinaryRows
open Cache Language SymbolicGraphView InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepthMeaning (DeepOrdinary)
open SourcePreparedSharedRows (read reference encode exposure interpretedEdge)
open InternedGuardedLanguage (meaning Env)

/-- The current ordinary snapshot retains exact ordered rows and full constraints. -/
def heap (state : State Symbol Guard) : SourceInternedRows.Heap Symbol Guard :=
  fun identity => ((read state identity).toList.flatMap nodeEdges).map exposure

/-- An available ordinary payload is exposed under its actual native identity. -/
theorem heap_node (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry edges depth free)) :
    heap state entry.identity = edges.map exposure := by
  have found := SourcePreparedSharedRows.read_identity state facts (.node entry edges depth free)
    available entry.identity rfl
  simp only [heap, found, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, nodeEdges]

/-- Native row children retain their exact current available payloads. -/
theorem child_available (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (available : Available state value) (edge : EdgeValue Symbol Guard) (member : edge ∈ nodeEdges value)
    (child : Value Symbol Guard) (inside : child ∈ edge.children) : Available state child :=
  facts.cached.edges edge.entry.key edge (resident_edges state facts.linked value available.resident edge member) child inside

/-- The current issued counter contains all dependencies of the ordinary snapshot. -/
theorem heap_closed (state : State Symbol Guard) (facts : Facts state) :
    SourceInternedRows.ClosedDomain (heap state) (List.range state.nodes.next) := by
  intro identity _ child member
  have pending := (SourceInternedRows.mem_successors (heap state) identity child).mp member
  obtain ⟨row, present, inside⟩ := List.mem_flatMap.mp pending
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp present
  obtain ⟨value, valueIn, edgeIn⟩ := List.mem_flatMap.mp edgeIn
  have found : read state identity = some value := Option.mem_toList.mp valueIn
  have available := SourcePreparedSharedRows.read_available state facts identity value found
  obtain ⟨childValue, childIn, same⟩ := List.mem_map.mp inside
  exact List.mem_range.mpr (SourcePreparedSharedRows.reference_bounded state facts childValue
    (child_available state facts value available edge edgeIn childValue childIn) child same)

/-- Available roots have one stable finite traversal of this same current snapshot. -/
theorem toRows_finite (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (available : Available state value) :
    ∃ fuel raw, ∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap state) larger (reference value) = some raw := by
  apply SourceInternedRows.toRows_finite (heap state) (List.range state.nodes.next) (heap_closed state facts)
  intro identity same
  exact List.mem_range.mpr (SourcePreparedSharedRows.reference_bounded state facts value available identity same)

/-- The graph retains each actual ordinary symbol, child reference, and full guard. -/
theorem graph_node (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry edges depth free)) (holds : Guard → Term Symbol → Bool) :
    SourceInternedRows.graph (heap state) holds (encode (.node entry edges depth free)) =
      edges.map (fun edge => renameEdge encode (interpretedEdge holds edge)) := by
  simp only [encode, reference, SourceInternedRows.stateOf, SourceInternedRows.graph,
    heap_node state facts entry edges depth free available, List.map_map]
  apply List.map_congr_left
  intro edge _
  simp only [Function.comp_apply, SourceInternedRows.interpret, SourceInternedRows.transition,
    exposure, renameEdge, interpretedEdge, List.map_map]
  rfl

/-- The same recursively ordinary component has exactly its independent guarded language. -/
theorem language_exact (state : State Symbol Guard) (semantic : SemanticReady state)
    (value : Value Symbol Guard) (available : Available state value) (deep : DeepOrdinary value)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (term : Term Symbol) :
    Accepts (SourceInternedRows.graph (heap state) holds) (encode value) term ↔
      meaning holds ambient value term := by
  let facts := semantic.ready.semantic.1.normal.facts
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → DeepOrdinary value →
      (Accepts (SourceInternedRows.graph (heap state) holds) (encode value) term ↔
        meaning holds ambient value term)) generalizing value with
  | node symbol children ih =>
      cases deep with
      | empty =>
          constructor
          · intro accepted
            exact False.elim (SourceInternedRows.empty_rejects (heap state) holds (.node symbol children) accepted)
          · intro accepted
            exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty (.node symbol children) accepted)
      | node entry edges depth free deepChildren =>
          rw [Language.accepts_node_iff, graph_node state facts entry edges depth free available holds,
            (InternedGuardedLanguage.laws holds ambient).node]
          constructor
          · rintro ⟨edge, member, label, runs, guard⟩
            obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
            have mapped := (all₂_map_iff _ encode original.children children).mp runs
            refine ⟨original, present, children, ?_, ?_, guard⟩
            · exact congrArg (fun label => Term.node label children) label.symm
            · apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ mapped
              intro child childIn term termIn accepted
              exact (ih term termIn child
                (child_available state facts (.node entry edges depth free) available original present child childIn)
                (deepChildren original present child childIn)).mp accepted
          · rintro ⟨edge, member, terms, root, runs, guard⟩
            have sameTerms : terms = children := (Term.node.inj root).2.symm
            subst terms
            have label : edge.entry.key.symbol = symbol := (Term.node.inj root).1.symm
            refine ⟨renameEdge encode (interpretedEdge holds edge), List.mem_map.mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
            apply (all₂_map_iff _ encode edge.children children).mpr
            apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
            intro child childIn term termIn accepted
            exact (ih term termIn child
              (child_available state facts (.node entry edges depth free) available edge member child childIn)
              (deepChildren edge member child childIn)).mpr accepted
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available deep
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available deep
      · exact tail term member value available deep

/-- The actual completed finite table has the same full-guard component language. -/
theorem table_language (state : State Symbol Guard) (semantic : SemanticReady state)
    (value : Value Symbol Guard) (available : Available state value) (deep : DeepOrdinary value)
    (fuel : Nat) (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (done : SourceInternedRows.toRows (heap state) fuel (reference value) = some raw)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (term : Term Symbol) :
    Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw)) (encode value) term ↔
      meaning holds ambient value term :=
  (SourceInternedRows.toRows_language (heap state) holds fuel (reference value) raw done term).trans
    (language_exact state semantic value available deep holds ambient term)

/-- Current native payloads derive one finite stable table with exact guarded language. -/
theorem finite (state : State Symbol Guard) (semantic : SemanticReady state)
    (value : Value Symbol Guard) (available : Available state value) (deep : DeepOrdinary value) :
    ∃ fuel raw,
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap state) larger (reference value) = some raw) ∧
      ∀ holds ambient term,
        Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw)) (encode value) term ↔
          meaning holds ambient value term := by
  obtain ⟨fuel, raw, stable⟩ := toRows_finite state semantic.ready.semantic.1.normal.facts value available
  exact ⟨fuel, raw, stable, fun holds ambient term =>
    table_language state semantic value available deep fuel raw (stable fuel (Nat.le_refl _)) holds ambient term⟩

end MicroCFTA.SourceNativeOrdinaryRows
