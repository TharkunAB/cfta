import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Constructor language laws with arbitrary recursive leaves

The laws use only EmptyNode, ordinary nodes, and explicit unions.
They leave recursive values as an arbitrary language parameter.
-/
namespace MicroCFTA.MergedColdInterpretation
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedUnionRetention InternedUnionFilterFusion EqualityLeafProjectionPhysical Language

/-- An edge retains its label, guard, and ordered child languages. -/
def EdgeMeaning (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ lang edge.children terms ∧
    meaning edge.entry.key.constraint term = true

/-- Ordinary constructor laws do not prescribe the language of recursive leaves. -/
structure Laws (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) : Prop where
  empty : ∀ term, ¬ lang .empty term
  node : ∀ entry edges depth free term, lang (.node entry edges depth free) term ↔
    ∃ edge ∈ edges, EdgeMeaning lang meaning edge term
  union : ∀ entry members depth free term, lang (.union entry members depth free) term ↔
    ∃ member ∈ members, lang member term

/-- An accepted edge has no literal empty child. -/
theorem accepted_live [DecidableEq (EdgeKey Symbol Guard)]
    (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning) (edge : EdgeValue Symbol Guard) (term : Term Symbol)
    (accepted : EdgeMeaning lang meaning edge term) : dead edge = false := by
  obtain ⟨terms, _, runs, _⟩ := accepted
  apply Bool.eq_false_iff.mpr
  intro isDead
  obtain ⟨child, included, empty⟩ := List.any_eq_true.mp isDead
  have same : child = .empty := (reference_empty child).mp (beq_iff_eq.mp empty)
  obtain ⟨subterm, _, childRun⟩ := SymbolicSmartRows.all₂_child _ _ _ runs child included
  rw [same] at childRun
  exact laws.empty subterm childRun

/-- Canonical ordering and dead-edge removal preserve the exact edge language. -/
theorem normalized_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (lang : Value Symbol Guard → Term Symbol → Prop)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning) (term : Term Symbol) :
    (∃ edge ∈ canonicalEdges (surviving edges), EdgeMeaning lang meaning edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning lang meaning edge term := by
  constructor
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, ((normalized_member state facts.coherent edges resident edge).mp member).1, accepted⟩
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, (normalized_member state facts.coherent edges resident edge).mpr
      ⟨member, accepted_live lang meaning laws edge term accepted⟩, accepted⟩

/-- Actual ordinary node construction has the requested edge language in any common cache. -/
theorem makeNode_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (lang : Value Symbol Guard → Term Symbol → Prop)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning) (term : Term Symbol) :
    lang (run (makeNode edges) state).1 term ↔
      ∃ edge ∈ edges, EdgeMeaning lang meaning edge term := by
  rw [← normalized_exact state facts lang edges resident meaning laws term]
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil => simp [makeNode, kept, run, laws.empty]
  | cons first rest =>
      obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
        (by simpa only [Edges, kept] using selected)
      simp only [makeNode, kept, run, readback, identifyNode]
      exact laws.node entry _ _ _ term

/-- Flattening a stored union keeps its exact operand language. -/
theorem flatten_one [DecidableEq (EdgeKey Symbol Guard)]
    (lang : Value Symbol Guard → Term Symbol → Prop) (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning)
    (value : Value Symbol Guard) (term : Term Symbol) :
    (∃ member ∈ unionMembers value, lang member term) ↔
      lang value term := by
  cases value with
  | empty => simp [unionMembers, laws.empty]
  | reference | node | mu => simp only [unionMembers, List.mem_singleton, exists_eq_left]
  | union entry members depth free => exact (laws.union entry members depth free term).symm

/-- Flattening and physical identity deduplication preserve the exact operand language. -/
theorem selected_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (lang : Value Symbol Guard → Term Symbol → Prop)
    (values : List (Value Symbol Guard)) (inputs : Values state values)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning) (term : Term Symbol) :
    (∃ member ∈ distinctNodes (values.flatMap unionMembers), lang member term) ↔
      ∃ member ∈ values, lang member term := by
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (inputs source original) value selected
  constructor
  · rintro ⟨member, present, accepted⟩
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ member present)
    exact ⟨source, original, (flatten_one lang meaning laws source term).mp ⟨member, selected, accepted⟩⟩
  · rintro ⟨source, original, accepted⟩
    obtain ⟨member, selected, accepted⟩ := (flatten_one lang meaning laws source term).mpr accepted
    exact ⟨member, distinctNodes_retains state facts.coherent _
      (fun value included => (flatAvailable value included).resident) member
      (List.mem_flatMap.mpr ⟨source, original, selected⟩), accepted⟩

/-- The ordinary fast path concatenates exactly the operand edge languages. -/
theorem ordinary_exact [DecidableEq (EdgeKey Symbol Guard)]
    (lang : Value Symbol Guard → Term Symbol → Prop) (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning)
    (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) (term : Term Symbol) :
    (∃ edge ∈ edges, EdgeMeaning lang meaning edge term) ↔
      ∃ value ∈ values, lang value term := by
  induction values generalizing edges with
  | nil => simp only [ordinaryEdges, Option.some.injEq] at found; subst edges; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      rename_i entry own depth free
      cases tail : ordinaryEdges rest with
      | none => simp [tail] at found
      | some later =>
          simp only [tail, Option.map_some, Option.some.injEq] at found
          subst edges
          simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro ⟨edge, before | after, accepted⟩
            · exact ⟨_, Or.inl rfl, (laws.node entry own depth free term).mpr ⟨edge, before, accepted⟩⟩
            · obtain ⟨value, member, accepted⟩ := (ih later tail).mp ⟨edge, after, accepted⟩
              exact ⟨value, Or.inr member, accepted⟩
          · rintro ⟨value, same | member, accepted⟩
            · subst value
              obtain ⟨edge, member, accepted⟩ := (laws.node entry own depth free term).mp accepted
              exact ⟨edge, Or.inl member, accepted⟩
            · obtain ⟨edge, member, accepted⟩ := (ih later tail).mpr ⟨value, member, accepted⟩
              exact ⟨edge, Or.inr member, accepted⟩

/-- Actual union readback denotes exactly its original operands in any common cache. -/
theorem makeUnion_common [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (lang : Value Symbol Guard → Term Symbol → Prop)
    (values : List (Value Symbol Guard)) (inputs : Values state values)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning) (term : Term Symbol) :
    lang (run (makeUnion values) state).1 term ↔
      ∃ value ∈ values, lang value term := by
  rw [← selected_exact state facts lang values inputs meaning laws term]
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, selected, run, laws.empty]
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion, selected, run, List.mem_singleton, exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry, readback⟩ := union_readback values first second tail state facts inputs selected ordinary
              rw [readback]
              exact laws.union entry _ _ _ term
          | some edges =>
              have available : Values state (first :: second :: tail) := by
                simpa only [selected] using selected_available values state inputs
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (available value member).resident) ordinary
              simp only [makeUnion, selected, ordinary]
              exact (makeNode_exact state facts lang edges resident meaning laws term).trans
                (ordinary_exact lang meaning laws _ edges ordinary term)

end MicroCFTA.MergedColdInterpretation
