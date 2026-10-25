import MicroCFTA.InternedFreshProbeKeys

/-!
# Probe provenance through actual constructor effects

Constructor inputs retain resident records and issued reference names.
Cache readback preserves these properties for the complete child records.
No probe-level provenance law is assumed.
-/
namespace MicroCFTA.InternedProbeProvenance
open Cache InternedBinderProtocol InternedConstructorTemplates InternedRecordCoherence InternedFreshProbeKeys

/-- All immediate records retained by a source node, including both stored Mu probes. -/
def children : Value Symbol Guard → List (Value Symbol Guard)
  | .empty | .reference _ => []
  | .node _ edges _ _ => edges.flatMap EdgeValue.children
  | .union _ members _ _ => members
  | .mu _ body depth ordinary => [body, depth, ordinary]

/-- Actual source inputs retain their resident records and earlier reference reservations recursively. -/
inductive Available (state : InternedConstructorTemplates.State Symbol Guard) : Value Symbol Guard → Prop where
  | intro (value : Value Symbol Guard) (resident : Resident state value)
      (issued : IssuedReferences state.nodes value)
      (children : ∀ child ∈ children value, Available state child) : Available state value

/-- A constructor's payload needs no independent assumption about its future parent entry. -/
def Contents (state : InternedConstructorTemplates.State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  IssuedReferences state.nodes value ∧ ∀ child ∈ children value, Available state child

/-- Every complete stored record retains the same recursively available children. -/
structure Cached (state : InternedConstructorTemplates.State Symbol Guard) : Prop where
  edges : ∀ key edge, state.edgeRecords key = some edge → ∀ child ∈ edge.children, Available state child
  nodes : ∀ key value, state.nodeRecords key = some value → Available state value

/-- No cached input obligations remain in the empty constructor state. -/
theorem empty_cached : Cached (empty (Symbol := Symbol) (Guard := Guard)) := by
  constructor <;> intro key value impossible <;> cases impossible

/-- Availability exposes the exact residency needed by canonical probe-key separation. -/
theorem Available.resident (available : Available state value) : Resident state value := by
  cases available with | intro _ resident _ _ => exact resident

/-- Availability exposes actual issued-name provenance, including false or erased branches. -/
theorem Available.issued (available : Available state value) : IssuedReferences state.nodes value := by
  cases available with | intro _ _ issued _ => exact issued

/-- Each retained child is available independently of whether its parent later survives normalization. -/
theorem Available.children (available : Available state value) : ∀ child ∈ children value, Available state child := by
  cases available with | intro _ _ _ children => exact children

/-- Record growth and reservation growth preserve all recursively retained inputs. -/
theorem Available.grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (growth : Grows before after) (issuedGrowth : Extends before.nodes.issued after.nodes.issued)
    (available : Available before value) : Available after value := by
  induction available with
  | intro value resident issued children ih =>
      refine .intro value (resident_grows before after growth value resident) ?_ ih
      intro identity member
      obtain ⟨key, present⟩ := issued identity member
      exact ⟨key, issuedGrowth identity key present⟩

/-- Constructor contents grow with the actual record and reservation histories. -/
theorem contents_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (growth : Grows before after) (issuedGrowth : Extends before.nodes.issued after.nodes.issued)
    (contents : Contents before value) : Contents after value := by
  constructor
  · intro identity member
    obtain ⟨key, present⟩ := contents.1 identity member
    exact ⟨key, issuedGrowth identity key present⟩
  · exact fun child member => (contents.2 child member).grows before after growth issuedGrowth

/-- Every actual generated effect preserves the node reference reservation history. -/
theorem run_issued_extends [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    Extends state.nodes.issued (run work state).2.nodes.issued := by
  induction work generalizing state with
  | pure value => exact extends_refl _
  | edge key identify resume ih =>
      exact ih _ _ (edgeStep_correct key identify state valid).1
  | node key identify resume ih =>
      exact extends_trans (intern_issued_extends state.nodes key valid.2)
        (ih _ _ (nodeStep_correct key identify state valid).1)

/-- Available input records remain available after any valid constructor computation. -/
theorem available_after_run [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (available : Available state value) : Available (run work state).2 value :=
  available.grows state _ (InternedConstructorTemplates.run_correct work state valid).2
    (run_issued_extends work state valid)

/-- EmptyNode has no record or reference obligations. -/
theorem empty_available (state : InternedConstructorTemplates.State Symbol Guard) : Available state .empty := by
  refine .intro _ ?_ ?_ ?_
  · intro entry impossible; cases impossible
  · intro identity impossible; cases impossible
  · intro child impossible; cases impossible

/-- A primitive reference is available exactly when its interned names have been reserved. -/
theorem reference_available (state : InternedConstructorTemplates.State Symbol Guard) (name : Reference)
    (issued : IssuedReferences (Symbol := Symbol) (Guard := Guard) state.nodes (.reference name)) :
    Available state (.reference name) := by
  refine .intro _ ?_ issued ?_
  · intro entry impossible; cases impossible
  · intro child impossible; cases impossible

/-- Node readback derives residency and retains only locally supplied constructor contents. -/
theorem nodeStep_available (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (fields : ∀ entry, entry.key = key → NodeFields key entry (identify entry))
    (contents : ∀ entry, entry.key = key → Contents state (identify entry)) :
    Coherent (nodeStep key identify state).2 ∧ Cached (nodeStep key identify state).2 ∧
      Available (nodeStep key identify state).2 (nodeStep key identify state).1 := by
  have correct := nodeStep_correct key identify state coherent.valid
  have finalCoherent := nodeStep_coherent key identify state coherent fields
  have history := intern_issued_extends state.nodes key coherent.valid.2
  have finalCached : Cached (nodeStep key identify state).2 := by
    constructor
    · intro other edge stored child member
      exact (cached.edges other edge stored child member).grows _ _ correct.2.1 history
    · intro other value stored
      rcases record_cases state.nodeRecords key other _ value stored with old | ⟨same, sameValue⟩
      · exact (cached.nodes other value old).grows _ _ correct.2.1 history
      · subst other value
        have retained := contents_grows state _ correct.2.1 history
          (contents _ (Cache.intern_correct state.nodes key coherent.valid.2).2.2)
        exact .intro _ (stored_resident _ finalCoherent key _ stored) retained.1 retained.2
  exact ⟨finalCoherent, finalCached, finalCached.nodes key _ correct.2.2⟩

/-- Edge readback retains complete available children from the actual first-writer payload. -/
theorem edgeStep_available [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (fields : ∀ entry, entry.key = key → (identify entry).entry = entry ∧ EdgeFields key (identify entry))
    (contents : ∀ entry, entry.key = key → ∀ child ∈ (identify entry).children, Available state child) :
    Coherent (edgeStep key identify state).2 ∧ Cached (edgeStep key identify state).2 ∧
      ∀ child ∈ (edgeStep key identify state).1.children, Available (edgeStep key identify state).2 child := by
  have correct := edgeStep_correct key identify state coherent.valid
  have finalCoherent := edgeStep_coherent key identify state coherent fields
  have finalCached : Cached (edgeStep key identify state).2 := by
    constructor
    · intro other edge stored child member
      rcases record_cases state.edgeRecords key other _ edge stored with old | ⟨same, sameValue⟩
      · exact (cached.edges other edge old child member).grows _ _ correct.2.1 (extends_refl _)
      · subst other edge
        exact (contents _ (Cache.intern_correct state.edges key coherent.valid.1).2.2 child member).grows
          _ _ correct.2.1 (extends_refl _)
    · intro other value stored
      exact (cached.nodes other value stored).grows _ _ correct.2.1 (extends_refl _)
  exact ⟨finalCoherent, finalCached, finalCached.edges key _ correct.2.2⟩

/-- The generated edge request keeps only its actual available child records. -/
theorem makeEdge_available [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : ∀ value ∈ values, Available state value) :
    Coherent (run (makeEdge symbol constraint values) state).2 ∧
      Cached (run (makeEdge symbol constraint values) state).2 ∧
      ∀ child ∈ (run (makeEdge symbol constraint values) state).1.children,
        Available (run (makeEdge symbol constraint values) state).2 child := by
  simpa only [makeEdge, InternedConstructorTemplates.run] using edgeStep_available
    ⟨symbol, values.map Value.referenceOf, constraint⟩ (fun entry => .mk entry values) state coherent cached
    (fun _ found => ⟨rfl, found, rfl⟩) (fun _ _ => available)

/-- Canonical edge sorting selects complete edges from the original source list. -/
theorem canonicalEdges_member (edges : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ canonicalEdges edges) : edge ∈ edges := by
  obtain ⟨identity, _, selected⟩ := List.mem_filterMap.mp member
  exact List.mem_of_find?_eq_some selected

/-- Empty-child removal and sorting retain the provenance of each surviving child. -/
theorem normalized_children (edges : List (EdgeValue Symbol Guard))
    (available : ∀ child ∈ edges.flatMap EdgeValue.children, Available state child) :
    ∀ child ∈ (canonicalEdges (surviving edges)).flatMap EdgeValue.children, Available state child := by
  intro child member
  obtain ⟨edge, present, found⟩ := List.mem_flatMap.mp member
  have original := (List.mem_filter.mp (canonicalEdges_member _ edge present)).1
  exact available child (List.mem_flatMap.mpr ⟨edge, original, found⟩)

/-- Ordinary node compilation derives residency and provenance after its source normalization. -/
theorem makeNode_available [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ child ∈ edges.flatMap EdgeValue.children, Available state child) :
    Coherent (run (makeNode edges) state).2 ∧ Cached (run (makeNode edges) state).2 ∧
      Available (run (makeNode edges) state).2 (run (makeNode edges) state).1 := by
  have normalized := normalized_children edges available
  unfold makeNode
  dsimp only
  split
  · exact ⟨coherent, cached, empty_available state⟩
  · rename_i first rest same
    apply nodeStep_available _ _ state coherent cached
    · intro entry _; exact ⟨rfl, rfl, rfl, rfl⟩
    · intro entry _
      have retained : ∀ child ∈ (first :: rest).flatMap EdgeValue.children, Available state child := by
        simpa only [same] using normalized
      exact ⟨identifyNode_issued state.nodes _ entry (fun child member => (retained child member).issued), retained⟩

/-- Union flattening reads only a complete available member or one of its retained children. -/
theorem unionMembers_available (value : Value Symbol Guard) (available : Available state value) :
    ∀ child ∈ unionMembers value, Available state child := by
  cases value with
  | empty => simp [unionMembers]
  | union entry members depth free => exact available.children
  | reference name | node entry edges depth free | mu entry body depth ordinary =>
      simpa only [unionMembers, List.mem_singleton, forall_eq] using available

/-- Identity deduplication cannot introduce a new input record. -/
theorem distinctNodes_member (values : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (member : value ∈ distinctNodes values) : value ∈ values := by
  cases values with
  | nil => simp [distinctNodes] at member
  | cons first rest =>
      simp only [distinctNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact List.mem_cons_self
      · have retained := distinctNodes_member (rest.filter (fun other => other.referenceOf != first.referenceOf)) value member
        exact List.mem_cons_of_mem _ (List.mem_filter.mp retained).1
termination_by values.length
decreasing_by simp_wf; have := List.length_filter_le (fun other => other.referenceOf != first.referenceOf) rest; simp_all; omega

/-- The ordinary-union fast path reads only children retained by its actual member records. -/
theorem ordinaryEdges_available (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (available : ∀ value ∈ values, Available state value) (selected : ordinaryEdges values = some edges) :
    ∀ child ∈ edges.flatMap EdgeValue.children, Available state child := by
  induction values generalizing edges with
  | nil => cases selected; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at selected <;> try contradiction
      case node entry original depth free =>
        cases found : ordinaryEdges rest with
        | none => simp [found] at selected
        | some tail =>
            have same : original ++ tail = edges := by simpa [found] using selected
            subst edges
            intro child member
            simp only [List.flatMap_append, List.mem_append] at member
            rcases member with head | tailMember
            · exact (available _ List.mem_cons_self).children child head
            · exact ih tail (fun value member => available value (List.mem_cons_of_mem _ member)) found child tailMember

/-- Every source union branch retains residency and issued references after flattening and deduplication. -/
theorem makeUnion_available [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) :
    Coherent (run (makeUnion values) state).2 ∧ Cached (run (makeUnion values) state).2 ∧
      Available (run (makeUnion values) state).2 (run (makeUnion values) state).1 := by
  have retained : ∀ child ∈ distinctNodes (values.flatMap unionMembers), Available state child := by
    intro child member
    obtain ⟨value, present, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ _ member)
    exact unionMembers_available value (available value present) child selected
  unfold makeUnion
  split
  · exact ⟨coherent, cached, empty_available state⟩
  · rename_i value same
    exact ⟨coherent, cached, retained value (by simp [same])⟩
  · split
    · rename_i edges found
      exact makeNode_available edges state coherent cached
        (ordinaryEdges_available _ edges retained found)
    · simpa only [InternedConstructorTemplates.run] using nodeStep_available
        (.union ((distinctNodes (values.flatMap unionMembers)).map Value.referenceOf))
        (fun entry => .union entry (distinctNodes (values.flatMap unionMembers))
          (maximumDepth (distinctNodes (values.flatMap unionMembers)))
          (childFree (distinctNodes (values.flatMap unionMembers)))) state coherent cached
        (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
        (fun entry _ => ⟨identifyUnion_issued state.nodes _ entry
          (fun child member => (retained child member).issued), retained⟩)

end MicroCFTA.InternedProbeProvenance
