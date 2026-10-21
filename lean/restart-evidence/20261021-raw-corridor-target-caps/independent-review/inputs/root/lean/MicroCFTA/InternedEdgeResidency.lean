import MicroCFTA.InternedUnionSeparation

/-!
# Resident edge payloads inside stored ordinary nodes

Node keys contain edge identities. This additional invariant connects each
stored edge payload to the complete canonical edge record. It prevents a
cache-hit proof from using an identity with unrelated ordered children.
-/
namespace MicroCFTA.InternedEdgeResidency
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys
open InternedBinderProtocol (NodeKey)

/-- Read only the actual outgoing edge payloads of an ordinary node. -/
def nodeEdges : Value Symbol Guard → List (EdgeValue Symbol Guard)
  | .node _ edges _ _ => edges
  | _ => []

/-- An edge payload is the complete canonical record under its own key. -/
def EdgeResident (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  state.edgeRecords edge.entry.key = some edge

/-- Each edge retained in a stored ordinary node has its canonical payload. -/
def Linked (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value →
    ∀ edge ∈ nodeEdges value, EdgeResident state edge

/-- The initial source tables contain no unlinked edge payload. -/
theorem empty_linked : Linked (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Actual table growth retains complete edge payloads. -/
theorem edge_grows (before after : State Symbol Guard) (growth : Grows before after)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident before edge) : EdgeResident after edge :=
  growth.edgeRecords edge.entry.key edge resident

/-- Residency of the parent gives residency of every actual outgoing edge. -/
theorem resident_edges (state : State Symbol Guard) (linked : Linked state)
    (value : Value Symbol Guard) (resident : Resident state value) :
    ∀ edge ∈ nodeEdges value, EdgeResident state edge := by
  cases value <;> simp only [nodeEdges] <;> try simp
  case node entry edges depth free => exact linked entry.key _ (resident entry rfl)

/-- Adding an edge record preserves every link from an existing node. -/
theorem edgeStep_linked [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) (linked : Linked state) :
    Linked (edgeStep key identify state).2 := by
  intro other value stored edge member
  have original : state.nodeRecords other = some value := stored
  exact edge_grows state _ (edgeStep_correct key identify state valid).2.1 edge
    (linked other value original edge member)

/-- Adding a node record preserves all links when its own actual edge
payloads came from the canonical edge table. -/
theorem nodeStep_linked (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (linked : Linked state)
    (inputs : ∀ entry edge, edge ∈ nodeEdges (identify entry) → EdgeResident state edge) :
    Linked (nodeStep key identify state).2 := by
  intro other value stored edge member
  rcases record_cases _ key other _ value stored with old | ⟨same, equal⟩
  · exact linked other value old edge member
  · subst other value
    exact inputs _ edge member

/-- Source edge readback returns a resident payload, including existing entries. -/
theorem makeEdge_linked [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) :
    Linked (run (makeEdge symbol constraint values) state).2 ∧
      EdgeResident (run (makeEdge symbol constraint values) state).2
        (run (makeEdge symbol constraint values) state).1 := by
  let key : EdgeKey Symbol Guard := ⟨symbol, values.map Value.referenceOf, constraint⟩
  let identify := fun entry => EdgeValue.mk entry values
  have correct := edgeStep_correct key identify state coherent.valid
  have after := edgeStep_coherent key identify state coherent (fun _ found => ⟨rfl, found, rfl⟩)
  have fields := (after.edges key _ correct.2.2).2.1
  refine ⟨edgeStep_linked key identify state coherent.valid linked, ?_⟩
  change (edgeStep key identify state).2.edgeRecords
    (edgeStep key identify state).1.entry.key = some (edgeStep key identify state).1
  rw [fields]
  exact correct.2.2

/-- Node normalization selects only existing canonical edge payloads. -/
theorem makeNode_linked [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    Linked (run (makeNode edges) state).2 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact linked
  · rename_i first rest same
    apply nodeStep_linked _ _ state linked
    intro entry edge member
    exact selected edge (by simpa only [same, identifyNode, nodeEdges] using member)

/-- The ordinary union branch concatenates resident edge payloads. -/
theorem ordinaryEdges_resident (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) (found : ordinaryEdges values = some edges) :
    ∀ edge ∈ edges, EdgeResident state edge := by
  induction values generalizing edges with
  | nil => cases found; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry original depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : original ++ later = edges := by simpa [tail] using found
            subst edges
            intro edge member
            rcases List.mem_append.mp member with first | tailMember
            · exact resident_edges state linked (.node entry original depth free)
                (resident _ (by simp)) edge first
            · exact ih later (fun value present => resident value (by simp [present])) tail edge tailMember

/-- Every source union branch preserves the new edge-record invariant. -/
theorem makeUnion_linked [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) :
    Linked (run (makeUnion values) state).2 := by
  have retained : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Resident state value := by
    intro value member
    obtain ⟨original, present, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ _ member)
    exact (unionMembers_available original (available original present) value inner).resident
  unfold makeUnion
  split
  · exact linked
  · exact linked
  · split
    · exact makeNode_linked _ state linked (ordinaryEdges_resident _ _ state linked retained ‹_›)
    · simp only [run]
      apply nodeStep_linked _ _ state linked
      intro entry edge impossible
      simp [nodeEdges] at impossible

/-- Current root self-reference removal preserves all ordinary edge links. -/
theorem withoutSelfReference_linked [DecidableEq (EdgeKey Symbol Guard)]
    (name : InternedBinderProtocol.Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (linked : Linked state) (available : Available state value) :
    Linked (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact linked
  case union entry members depth free =>
    split
    · apply makeUnion_linked _ state linked
      intro value member
      exact available.children value (List.mem_filter.mp member).1
    · exact linked

/-- Equal edge identities determine the complete ordered child payload. -/
theorem edge_identity_unique (state : State Symbol Guard) (coherent : Coherent state)
    (first second : EdgeValue Symbol Guard) (left : EdgeResident state first)
    (right : EdgeResident state second) (same : first.entry.identity = second.entry.identity) : first = second := by
  have firstStored := (coherent.edges first.entry.key first left).1
  have secondStored := (coherent.edges second.entry.key second right).1
  have keys := (Cache.identity_eq_iff_key_eq state.edges coherent.valid.1 firstStored secondStored).mp same
  unfold EdgeResident at left right
  rw [← keys] at right
  exact Option.some.inj (left.symm.trans right)

/-- Equal canonical edge-identity lists retain the same complete payloads. -/
theorem edge_lists_equal (state : State Symbol Guard) (coherent : Coherent state)
    (first second : List (EdgeValue Symbol Guard))
    (left : ∀ edge ∈ first, EdgeResident state edge)
    (right : ∀ edge ∈ second, EdgeResident state edge)
    (same : first.map (fun edge => edge.entry.identity) = second.map (fun edge => edge.entry.identity)) :
    first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons head tail ih =>
      cases second with
      | nil => simp at same
      | cons other rest =>
          have parts := List.cons.inj same
          have headEq := edge_identity_unique state coherent head other (left head (by simp))
            (right other (by simp)) parts.1
          have tailEq := ih rest (fun edge member => left edge (by simp [member]))
            (fun edge member => right edge (by simp [member])) parts.2
          simp [headEq, tailEq]

/-- An ordinary cache hit returns the same complete canonical edge list as
the current request. This proof uses actual edge residency, not only keys. -/
theorem identifyNode_readback (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    ∃ entry, (nodeStep (.node (edges.map (fun edge => edge.entry.identity)))
      (identifyNode edges) state).1 = identifyNode edges entry := by
  let key := NodeKey.node (edges.map (fun edge => edge.entry.identity))
  let after := (nodeStep key (identifyNode edges) state).2
  let result := (nodeStep key (identifyNode edges) state).1
  have afterCoherent : Coherent after := nodeStep_coherent key (identifyNode edges) state coherent
    (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
  have afterLinked : Linked after := nodeStep_linked key (identifyNode edges) state linked
    (fun _ edge member => resident edge member)
  have stored : after.nodeRecords key = some result := (nodeStep_correct key (identifyNode edges) state coherent.valid).2.2
  obtain ⟨entry, _, fields⟩ := afterCoherent.nodes key result stored
  have actualEdges := afterLinked key result stored
  have expectedEdges : ∀ edge ∈ edges, EdgeResident after edge := resident
  cases found : result with
  | empty | reference | union | mu => simp [found, NodeFields, key, muKey] at fields
  | node actual original depth free =>
      simp only [found, NodeFields] at fields
      have equalIds : original.map (fun edge => edge.entry.identity) = edges.map (fun edge => edge.entry.identity) :=
        (NodeKey.node.inj fields.2.1).symm
      have equalEdges := edge_lists_equal after afterCoherent original edges
        (by simpa [found, nodeEdges] using actualEdges) expectedEdges equalIds
      refine ⟨actual, ?_⟩
      change result = identifyNode edges actual
      simp [found, identifyNode, equalEdges, fields.2.2.1, fields.2.2.2]

/-- Source mkNode returns exactly the child payloads of its surviving
canonical edges, including the empty result and existing node-cache hits. -/
theorem makeNode_children [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    InternedUnionSeparation.semanticChildren (run (makeNode edges) state).1 =
      (canonicalEdges (surviving edges)).flatMap EdgeValue.children := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp [run, InternedUnionSeparation.semanticChildren, same]
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, InternedUnionSeparation.semanticChildren, same]

/-- A resident edge is the unique complete payload selected by its identity. -/
theorem find_resident (state : State Symbol Guard) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (resident : ∀ value ∈ edges, EdgeResident state value) (member : edge ∈ edges) :
    edges.find? (fun value => value.entry.identity == edge.entry.identity) = some edge := by
  induction edges with
  | nil => simp at member
  | cons first rest ih =>
      by_cases same : first.entry.identity = edge.entry.identity
      · have equal := edge_identity_unique state coherent first edge (resident first (by simp))
          (resident edge member) same
        simp [List.find?, equal]
      · have inTail : edge ∈ rest := by
          rcases List.mem_cons.mp member with equal | present
          · subst first; exact False.elim (same rfl)
          · exact present
        have different : (first.entry.identity == edge.entry.identity) = false := by simp [same]
        simpa only [List.find?, different] using ih (fun value present => resident value (by simp [present])) inTail

/-- Canonical edge ordering preserves every resident input edge as a complete
payload. Identity duplicate removal cannot replace its child list. -/
theorem canonicalEdges_retains (state : State Symbol Guard) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (resident : ∀ value ∈ edges, EdgeResident state value) (member : edge ∈ edges) :
    edge ∈ canonicalEdges edges := by
  apply List.mem_filterMap.mpr
  refine ⟨edge.entry.identity, ?_, find_resident state coherent edges edge resident member⟩
  apply EnumerationBuilderCaches.canonicalIds_member _ _ |>.mpr
  exact List.mem_map.mpr ⟨edge, member, rfl⟩

/-- A retained input below a live edge remains below the actual source node
after sorting, deduplication, empty-child removal, and cache readback. -/
theorem makeNode_retains [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (live : edge.children.any (fun child => child.referenceOf == .empty) = false)
    (child needle : Value Symbol Guard) (member : child ∈ edge.children)
    (retained : InternedUnionSeparation.Retains needle child) :
    InternedUnionSeparation.Retains needle (run (makeNode edges) state).1 := by
  have survives : edge ∈ surviving edges := by simp [surviving, present, live]
  have kept := canonicalEdges_retains state coherent (surviving edges) edge
    (fun value included => resident value (List.mem_filter.mp included).1) survives
  apply InternedUnionSeparation.Retains.step (child := child) ?_ retained
  rw [makeNode_children edges state coherent linked resident]
  exact List.mem_flatMap.mpr ⟨edge, kept, member⟩

end MicroCFTA.InternedEdgeResidency
