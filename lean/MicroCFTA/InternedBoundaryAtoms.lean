import MicroCFTA.InternedNonemptyRecords
import MicroCFTA.InternedNormalizationFree

/-!
# Reference and Mu identities below ordinary constructors

The profile follows ordinary children and union members. It stops at each
Mu and records that Mu identity. It records literal reference identities.
Ordinary node and edge identities do not occur in the profile.
-/
namespace MicroCFTA.InternedBoundaryAtoms
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedLiveEdges
open InternedUnionRetention InternedUnionDescendants InternedNormalizationFree
open InternedBinderProtocol (Reference NodeRef NodeKey)

mutual
/-- A boundary is a literal reference or a Mu reached through ordinary constructors. -/
def atoms : Value Symbol Guard → List NodeRef
  | .empty => []
  | .reference name => [.ref name]
  | .node _ edges _ _ => edgeAtoms edges
  | .union _ members _ _ => manyAtoms members
  | .mu entry _ _ _ => [.mu entry.identity]
termination_by value => sizeOf value

/-- Ordered members retain all of their boundary identities. -/
def manyAtoms : List (Value Symbol Guard) → List NodeRef
  | [] => []
  | first :: rest => atoms first ++ manyAtoms rest
termination_by values => sizeOf values

/-- Ordinary edges expose the boundaries of their ordered children. -/
def edgeAtoms : List (EdgeValue Symbol Guard) → List NodeRef
  | [] => []
  | .mk _ children :: rest => manyAtoms children ++ edgeAtoms rest
termination_by edges => sizeOf edges
end

/-- An ordered child occurrence keeps its original atom. -/
theorem many_member (values : List (Value Symbol Guard)) (item : NodeRef) :
    item ∈ manyAtoms values ↔ ∃ value ∈ values, item ∈ atoms value := by
  induction values with
  | nil => simp [manyAtoms]
  | cons first rest ih => simp [manyAtoms, ih]

/-- An edge occurrence comes from one of its complete ordered child records. -/
theorem edge_member (edges : List (EdgeValue Symbol Guard)) (item : NodeRef) :
    item ∈ edgeAtoms edges ↔ ∃ edge ∈ edges, ∃ child ∈ edge.children, item ∈ atoms child := by
  induction edges with
  | nil => simp [edgeAtoms]
  | cons first rest ih =>
      cases first with
      | mk entry children => simp [edgeAtoms, many_member, ih, EdgeValue.children]

/-- Root union flattening preserves the boundary set. -/
theorem flatten_atom (value : Value Symbol Guard) (item : NodeRef) :
    item ∈ atoms value ↔ ∃ member ∈ unionMembers value, item ∈ atoms member := by
  cases value with
  | empty => simp [atoms, unionMembers]
  | union => simpa only [atoms, unionMembers] using many_member _ item
  | reference | node | mu => simp [unionMembers]

/-- Actual ordinary cache readback retains the exact surviving occurrence list. -/
theorem makeNode_atoms [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    atoms (run (makeNode edges) state).1 = edgeAtoms (canonicalEdges (surviving edges)) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp [run, atoms, same, edgeAtoms]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked (by simpa [same] using selected)
    simp only [run, readback, identifyNode, atoms, same]

/-- Sorting, deduplication, and canonical readback retain each live edge boundary. -/
theorem makeNode_atom [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (live : edge.children.any (fun child => child.referenceOf == .empty) = false)
    (child : Value Symbol Guard) (member : child ∈ edge.children) (item : NodeRef)
    (occurrence : item ∈ atoms child) : item ∈ atoms (run (makeNode edges) state).1 := by
  rw [makeNode_atoms edges state coherent linked resident, edge_member]
  have survives : edge ∈ surviving edges := by simp [surviving, present, live]
  exact ⟨edge, canonicalEdges_retains state coherent _ edge
    (fun value included => resident value (List.mem_filter.mp included).1) survives, child, member, occurrence⟩

/-- Complete interned-union readback retains the actual requested members and their atoms. -/
theorem union_readback_atom (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (available : Available state result) (inputs : ∀ value ∈ members, Available state value)
    (source : Value Symbol Guard) (member : source ∈ members) (item : NodeRef)
    (occurrence : item ∈ atoms source) : item ∈ atoms result := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual originals depth free =>
      have ids := NodeKey.union.inj fields.2.1
      have same := value_lists_equal state coherent members originals
        (fun value member => (inputs value member).resident)
        (fun value member => (available.children value member).resident) ids
      simp only [atoms, ← same, many_member]
      exact ⟨source, member, occurrence⟩

/-- Every actual union branch retains each input boundary. -/
theorem makeUnion_atom [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value)
    (source : Value Symbol Guard) (member : source ∈ values) (item : NodeRef)
    (occurrence : item ∈ atoms source) : item ∈ atoms (run (makeUnion values) state).1 := by
  obtain ⟨source, inner, occurrence⟩ := (flatten_atom source item).mp occurrence
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value present
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp present
    exact unionMembers_available original (available original included) value selected
  have flattened : source ∈ values.flatMap unionMembers := List.mem_flatMap.mpr ⟨_, member, inner⟩
  have sourceAvailable := allAvailable source flattened
  have selected := distinctNodes_retains state coherent _ (fun value member => (allAvailable value member).resident) source flattened
  have normalizedAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value :=
    fun value member => allAvailable value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [normalized] at selected
  | cons first rest =>
      cases rest with
      | nil =>
          have same : source = first := by simpa [normalized] using selected
          simpa only [makeUnion, normalized, run, ← same] using occurrence
      | cons second tail =>
          have sourceMember : source ∈ first :: second :: tail := by simpa [normalized] using selected
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using normalizedAvailable
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              obtain ⟨sourceEntry, sourceEdges, sourceDepth, sourceFree, same, included⟩ :=
                ordinaryEdges_contains _ edges ordinaryResult source sourceMember
              subst source
              obtain ⟨edge, present, child, childMember, childCost⟩ := (edge_member sourceEdges item).mp (by simpa only [atoms] using occurrence)
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (memberAvailable value member).resident) ordinaryResult
              have edgeLive := resident_live state live _ sourceAvailable.resident edge present
              simpa only [makeUnion, normalized, ordinaryResult] using
                makeNode_atom edges state coherent linked resident edge (included edge present) edgeLive child childMember item childCost
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value present
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value present)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              simpa only [makeUnion, normalized, ordinaryResult, run] using
                union_readback_atom after afterCoherent members actual result fields output inputs source sourceMember item occurrence

/-- Concatenating ordinary edge lists concatenates their actual occurrence lists. -/
theorem edgeAtoms_append (first second : List (EdgeValue Symbol Guard)) :
    edgeAtoms (first ++ second) = edgeAtoms first ++ edgeAtoms second := by
  induction first with
  | nil => simp [edgeAtoms]
  | cons head tail ih => cases head; simp [edgeAtoms, ih, List.append_assoc]

/-- The source all-ordinary merge preserves the ordered pre-normalization occurrence list. -/
theorem ordinaryEdges_atoms (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) : edgeAtoms edges = manyAtoms values := by
  induction values generalizing edges with
  | nil => cases found; simp [edgeAtoms, manyAtoms]
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            subst edges
            simp only [edgeAtoms_append, manyAtoms, atoms, ih later tail]

/-- Every surviving ordinary output occurrence came from an actual requested edge child. -/
theorem makeNode_atom_origin [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (item : NodeRef)
    (occurrence : item ∈ atoms (run (makeNode edges) state).1) : item ∈ edgeAtoms edges := by
  rw [makeNode_atoms edges state coherent linked resident, edge_member] at occurrence
  obtain ⟨edge, selected, child, member, present⟩ := occurrence
  exact (edge_member edges item).mpr ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge selected)).1, child, member, present⟩

/-- Complete canonical union readback contains the exact requested member occurrence list. -/
theorem union_readback_atoms (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (available : Available state result) (inputs : ∀ value ∈ members, Available state value) :
    atoms result = manyAtoms members := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual originals depth free =>
      have same := value_lists_equal state coherent members originals
        (fun value member => (inputs value member).resident)
        (fun value member => (available.children value member).resident) (NodeKey.union.inj fields.2.1)
      simp only [atoms, same]

/-- Actual union normalization introduces no boundary identity. -/
theorem makeUnion_atom_origin [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (item : NodeRef)
    (occurrence : item ∈ atoms (run (makeUnion values) state).1) :
    ∃ value ∈ values, item ∈ atoms value := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have origin : ∀ value ∈ distinctNodes (values.flatMap unionMembers), item ∈ atoms value →
      ∃ source ∈ values, item ∈ atoms source := by
    intro value member present
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact ⟨source, included, (flatten_atom source item).mpr ⟨value, inner, present⟩⟩
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, atoms] at occurrence
  | cons first rest =>
      cases rest with
      | nil => exact origin first (by simp [normalized]) (by simpa only [makeUnion, normalized, run] using occurrence)
      | cons second tail =>
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have fromMember : ∀ value ∈ first :: second :: tail, item ∈ atoms value → ∃ source ∈ values, item ∈ atoms source :=
            fun value member => origin value (by simpa [normalized] using member)
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked (fun value member => (memberAvailable value member).resident) ordinaryResult
              have inputCost := makeNode_atom_origin edges state coherent linked resident item
                (by simpa only [makeUnion, normalized, ordinaryResult] using occurrence)
              rw [ordinaryEdges_atoms _ edges ordinaryResult, many_member] at inputCost
              obtain ⟨value, member, present⟩ := inputCost
              exact fromMember value member present
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value member
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value member)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have same := union_readback_atoms after afterCoherent members actual result fields output inputs
              simp only [makeUnion, normalized, ordinaryResult, run] at occurrence
              change item ∈ atoms result at occurrence
              rw [same, many_member] at occurrence
              obtain ⟨value, member, present⟩ := occurrence
              exact fromMember value member present

/-- Every live source union output has exactly its input boundary set. -/
theorem makeUnion_atom_iff [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value) (item : NodeRef) :
    item ∈ atoms (run (makeUnion values) state).1 ↔ ∃ value ∈ values, item ∈ atoms value :=
  ⟨makeUnion_atom_origin values state coherent cached linked available item,
    fun ⟨value, member, present⟩ => makeUnion_atom values state coherent cached linked live available value member item present⟩

/-- Actual ordinary normalization has exactly the atoms of its surviving original edges. -/
theorem makeNode_atom_iff [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (item : NodeRef) :
    item ∈ atoms (run (makeNode edges) state).1 ↔
      ∃ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false ∧
        ∃ child ∈ edge.children, item ∈ atoms child := by
  rw [makeNode_atoms edges state coherent linked resident, edge_member]
  constructor
  · rintro ⟨edge, selected, child, member, occurrence⟩
    have survived := List.mem_filter.mp (canonicalEdges_member _ edge selected)
    refine ⟨edge, survived.1, ?_, child, member, occurrence⟩
    simpa using survived.2
  · rintro ⟨edge, member, live, child, included, occurrence⟩
    have survived : edge ∈ surviving edges := by simp [surviving, member, live]
    exact ⟨edge, canonicalEdges_retains state coherent _ edge
      (fun edge present => resident edge (List.mem_filter.mp present).1) survived, child, included, occurrence⟩


end MicroCFTA.InternedBoundaryAtoms
