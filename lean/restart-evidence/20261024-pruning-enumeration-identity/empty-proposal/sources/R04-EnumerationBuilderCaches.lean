import MicroCFTA.EnumerationBuilderLanguage

/-!
# Edge-cache and node-cache constructor readback

Copied edges are interned in order. The node constructor removes edges with
an empty child. It sorts and deduplicates the surviving edge identities,
then interns that list. Empty output has no node-cache identity.
-/
namespace MicroCFTA.EnumerationBuilderCaches
open Language EnumerationState EnumerationSemantics EnumerationCorrectness

/-- The source node key is the ascending set of its edge identities. -/
def canonicalIds (identities : List Nat) : List Nat := identities.eraseDups.mergeSort (· ≤ ·)

theorem canonicalIds_member (identities : List Nat) (identity : Nat) :
    identity ∈ canonicalIds identities ↔ identity ∈ identities := by
  simp [canonicalIds]

theorem canonicalIds_nodup (identities : List Nat) : (canonicalIds identities).Nodup := by
  exact (List.mergeSort_perm _ _).symm.nodup (EqualityTrie.eraseDups_nodup _)

theorem canonicalIds_sorted (identities : List Nat) : (canonicalIds identities).Pairwise (· ≤ ·) := by
  simpa [canonicalIds] using List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) identities.eraseDups

/-- Node keys are equal exactly when they contain the same edge identities. -/
theorem canonicalIds_equal (left right : List Nat) :
    canonicalIds left = canonicalIds right ↔ ∀ identity, identity ∈ left ↔ identity ∈ right := by
  constructor
  · intro same identity
    rw [← canonicalIds_member left identity, same, canonicalIds_member]
  · intro members
    apply List.Perm.eq_of_pairwise (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
      (canonicalIds_sorted left) (canonicalIds_sorted right)
    apply (List.perm_ext_iff_of_nodup (canonicalIds_nodup left) (canonicalIds_nodup right)).mpr
    intro identity
    simpa only [canonicalIds_member] using members identity

/-- Sequential interning preserves issued identities and canonical table entries. -/
theorem intern_grows [DecidableEq Key] (state : Cache.State Key) (valid : Cache.Valid state) (key : Key) :
    Cache.Extends state.issued (Cache.intern state key).2.issued ∧
      Cache.Extends state.table (Cache.intern state key).2.table := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using And.intro (Cache.extends_refl state.issued) (Cache.extends_refl state.table)
  | none =>
    exact ⟨by simpa [Cache.intern, found, Cache.install] using Cache.reserve_extends state key valid,
      by simpa [Cache.intern, found, Cache.install, Cache.reserve] using Cache.keepFirst_extends state.table key ⟨state.next, key⟩⟩

/-- A completed interning call returns an identity issued for exactly its key. -/
theorem intern_issued [DecidableEq Key] (state : Cache.State Key) (valid : Cache.Valid state) (key : Key) :
    (Cache.intern state key).2.issued (Cache.intern state key).1.identity = some key := by
  obtain ⟨safe, stored, _⟩ := Cache.intern_correct state key valid
  exact (safe.2 key _ stored).2

/-- Intern all copied edge keys in their source order. -/
def internAll [DecidableEq Key] : List Key → Cache.State Key → List (Cache.Interned Key) × Cache.State Key
  | [], state => ([], state)
  | key :: rest, state =>
      let first := Cache.intern state key
      let later := internAll rest first.2
      (first.1 :: later.1, later.2)

/-- The edge pass retains every key and leaves all returned entries canonical. -/
theorem internAll_correct [DecidableEq Key] (keys : List Key) (state : Cache.State Key) (valid : Cache.Valid state) :
    Cache.Valid (internAll keys state).2 ∧
      Cache.Extends state.issued (internAll keys state).2.issued ∧
      Cache.Extends state.table (internAll keys state).2.table ∧
      ((internAll keys state).1.map Cache.Interned.key = keys) ∧
      ∀ entry ∈ (internAll keys state).1, (internAll keys state).2.table entry.key = some entry := by
  induction keys generalizing state with
  | nil => exact ⟨valid, Cache.extends_refl _, Cache.extends_refl _, rfl, by simp [internAll]⟩
  | cons key rest ih =>
    obtain ⟨firstValid, firstStored, firstKey⟩ := Cache.intern_correct state key valid
    obtain ⟨firstIssuedGrowth, firstTableGrowth⟩ := intern_grows state valid key
    obtain ⟨lastValid, lastIssuedGrowth, lastTableGrowth, lastKeys, lastStored⟩ := ih _ firstValid
    refine ⟨lastValid, Cache.extends_trans firstIssuedGrowth lastIssuedGrowth,
      Cache.extends_trans firstTableGrowth lastTableGrowth, ?_, ?_⟩
    · simp only [internAll, List.map_cons, firstKey, lastKeys]
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rw [firstKey]
        exact lastTableGrowth _ _ firstStored
      · exact lastStored entry member

/-- Edge keys and node keys use separate canonical identity supplies. -/
structure Caches (Symbol Guard : Type) where
  edges : Cache.State (EnumerationState.Edge Symbol Guard)
  nodes : Cache.State (List Nat)

/-- A stored node key is nonempty, sorted, and refers only to canonical edges. -/
def NodeKeys (state : Caches Symbol Guard) : Prop :=
  ∀ identity ids, state.nodes.issued identity = some ids →
    ids ≠ [] ∧ canonicalIds ids = ids ∧
      ∀ edgeId ∈ ids, ∃ entry, state.edges.table entry.key = some entry ∧ entry.identity = edgeId

/-- The two caches retain their own canonical-key invariants. -/
structure Valid (state : Caches Symbol Guard) : Prop where
  edges : Cache.Valid state.edges
  nodes : Cache.Valid state.nodes
  keys : NodeKeys state

/-- Zero represents EmptyNode; a stored node identity is shifted by one. -/
def rows (state : Caches Symbol Guard) : Nat → List (EnumerationState.Edge Symbol Guard)
  | 0 => []
  | identity + 1 => ((state.nodes.issued identity).getD []).filterMap state.edges.issued

/-- The source node constructor sees the keys of already interned edges. -/
def surviving (entries : List (Cache.Interned (EnumerationState.Edge Symbol Guard))) :
    List (Cache.Interned (EnumerationState.Edge Symbol Guard)) :=
  entries.filter fun entry => !entry.key.children.contains 0

/-- Intern edges, discard empty-child edges, and intern the canonical node key. -/
def construct [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard) : Nat × Caches Symbol Guard :=
  let edgePass := internAll inputs state.edges
  let ids := canonicalIds ((surviving edgePass.1).map Cache.Interned.identity)
  match ids with
  | [] => (0, ⟨edgePass.2, state.nodes⟩)
  | first :: rest =>
      let nodePass := Cache.intern state.nodes (first :: rest)
      (nodePass.1.identity + 1, ⟨edgePass.2, nodePass.2⟩)

/-- Every returned edge identity reads its unchanged copied edge key. -/
theorem returned_edge [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Cache.State (EnumerationState.Edge Symbol Guard))
    (valid : Cache.Valid state) (entry : Cache.Interned (EnumerationState.Edge Symbol Guard))
    (member : entry ∈ (internAll inputs state).1) :
    (internAll inputs state).2.issued entry.identity = some entry.key := by
  have result := internAll_correct inputs state valid
  exact (result.1.2 entry.key entry (result.2.2.2.2 entry member)).2

/-- Reading the canonical identity set gives exactly the retained input rows. -/
theorem canonical_rows [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Cache.State (EnumerationState.Edge Symbol Guard))
    (valid : Cache.Valid state) (edge : EnumerationState.Edge Symbol Guard) :
    edge ∈ (canonicalIds ((surviving (internAll inputs state).1).map Cache.Interned.identity)).filterMap (internAll inputs state).2.issued ↔
      edge ∈ inputs ∧ 0 ∉ edge.children := by
  have result := internAll_correct inputs state valid
  constructor
  · intro present
    obtain ⟨identity, member, found⟩ := List.mem_filterMap.mp present
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp ((canonicalIds_member _ _).mp member)
    obtain ⟨listed, live⟩ := List.mem_filter.mp kept
    have issued := returned_edge inputs state valid entry listed
    rw [same] at issued
    have equal : entry.key = edge := Option.some.inj (issued.symm.trans found)
    constructor
    · rw [← result.2.2.2.1]
      exact List.mem_map.mpr ⟨entry, listed, equal⟩
    · simpa [equal] using live
  · rintro ⟨member, live⟩
    rw [← result.2.2.2.1] at member
    obtain ⟨entry, listed, same⟩ := List.mem_map.mp member
    apply List.mem_filterMap.mpr
    refine ⟨entry.identity, (canonicalIds_member _ _).mpr (List.mem_map.mpr ⟨entry, ?_, rfl⟩), ?_⟩
    · exact List.mem_filter.mpr ⟨listed, by simpa [same] using live⟩
    · simpa [same] using returned_edge inputs state valid entry listed

/-- The complete two-cache constructor derives exact source row readback. -/
theorem construct_rows [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (validEdges : Cache.Valid state.edges) (validNodes : Cache.Valid state.nodes) (edge : EnumerationState.Edge Symbol Guard) :
    edge ∈ rows (construct inputs state).2 (construct inputs state).1 ↔ edge ∈ inputs ∧ 0 ∉ edge.children := by
  have exactRows := canonical_rows inputs state.edges validEdges edge
  cases ids : canonicalIds ((surviving (internAll inputs state.edges).1).map Cache.Interned.identity) with
  | nil => simpa [construct, ids, rows] using exactRows
  | cons first rest =>
    have issued := intern_issued state.nodes validNodes (first :: rest)
    simpa [construct, ids, rows, issued] using exactRows

/-- Interning preserves a property of all issued keys when the new key has it. -/
theorem intern_property [DecidableEq Key] (property : Key → Prop) (state : Cache.State Key)
    (old : ∀ identity key, state.issued identity = some key → property key)
    (key : Key) (checked : property key) :
    ∀ identity actual, (Cache.intern state key).2.issued identity = some actual → property actual := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using old
  | none =>
    intro identity actual issued
    by_cases fresh : identity = state.next
    · have same : key = actual := by simpa [Cache.intern, found, Cache.install, Cache.reserve, fresh] using issued
      exact same ▸ checked
    · exact old identity actual (by simpa [Cache.intern, found, Cache.install, Cache.reserve, fresh] using issued)

/-- Each cache can grow without changing issued payloads or canonical entries. -/
structure Grows (before after : Caches Symbol Guard) : Prop where
  edgeIssued : Cache.Extends before.edges.issued after.edges.issued
  edgeTable : Cache.Extends before.edges.table after.edges.table
  nodeIssued : Cache.Extends before.nodes.issued after.nodes.issued
  nodeTable : Cache.Extends before.nodes.table after.nodes.table

/-- The two-stage constructor preserves both previous caches. -/
theorem construct_grows [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (validEdges : Cache.Valid state.edges) (validNodes : Cache.Valid state.nodes) : Grows state (construct inputs state).2 := by
  have edgePass := internAll_correct inputs state.edges validEdges
  cases ids : canonicalIds ((surviving (internAll inputs state.edges).1).map Cache.Interned.identity) with
  | nil => exact ⟨by simpa [construct, ids] using edgePass.2.1, by simpa [construct, ids] using edgePass.2.2.1, by simpa [construct, ids] using Cache.extends_refl state.nodes.issued,
      by simpa [construct, ids] using Cache.extends_refl state.nodes.table⟩
  | cons first rest =>
    have nodeGrowth := intern_grows state.nodes validNodes (first :: rest)
    exact ⟨by simpa [construct, ids] using edgePass.2.1, by simpa [construct, ids] using edgePass.2.2.1, by simpa [construct, ids] using nodeGrowth.1,
      by simpa [construct, ids] using nodeGrowth.2⟩

/-- Constructor output retains the canonical edge and node invariants. -/
theorem construct_valid [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (valid : Valid state) : Valid (construct inputs state).2 := by
  have edgePass := internAll_correct inputs state.edges valid.edges
  let property := fun ids : List Nat => ids ≠ [] ∧ canonicalIds ids = ids ∧
    ∀ identity ∈ ids, ∃ entry, (internAll inputs state.edges).2.table entry.key = some entry ∧ entry.identity = identity
  have old : ∀ identity ids, state.nodes.issued identity = some ids → property ids := by
    intro identity ids issued
    obtain ⟨nonempty, sorted, present⟩ := valid.keys identity ids issued
    refine ⟨nonempty, sorted, ?_⟩
    intro edgeId member
    obtain ⟨entry, stored, same⟩ := present edgeId member
    exact ⟨entry, edgePass.2.2.1 entry.key entry stored, same⟩
  cases ids : canonicalIds ((surviving (internAll inputs state.edges).1).map Cache.Interned.identity) with
  | nil =>
    exact ⟨by simpa [construct, ids] using edgePass.1, by simpa [construct, ids] using valid.nodes, by simpa [NodeKeys, construct, ids] using old⟩
  | cons first rest =>
    have checked : property (first :: rest) := by
      refine ⟨by simp, ?_, ?_⟩
      · rw [← ids]
        apply (canonicalIds_equal _ _).mpr
        intro identity
        exact canonicalIds_member _ identity
      · intro identity member
        rw [← ids, canonicalIds_member] at member
        obtain ⟨entry, retained, same⟩ := List.mem_map.mp member
        exact ⟨entry, edgePass.2.2.2.2 entry (List.mem_filter.mp retained).1, same⟩
    exact ⟨by simpa [construct, ids] using edgePass.1, by simpa [construct, ids] using (Cache.intern_correct state.nodes _ valid.nodes).1,
      by simpa [NodeKeys, construct, ids] using intern_property property state.nodes old (first :: rest) checked⟩

/-- A constructor result is empty or is the canonical entry for its stored node key. -/
def CanonicalNode (state : Caches Symbol Guard) (reference : Nat) : Prop :=
  reference = 0 ∨ ∃ key entry, state.nodes.table key = some entry ∧ reference = entry.identity + 1

/-- Every constructor result has its source-style canonical node representation. -/
theorem construct_canonical [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (validNodes : Cache.Valid state.nodes) : CanonicalNode (construct inputs state).2 (construct inputs state).1 := by
  cases ids : canonicalIds ((surviving (internAll inputs state.edges).1).map Cache.Interned.identity) with
  | nil => exact Or.inl (by simp [construct, ids])
  | cons first rest =>
    exact Or.inr ⟨first :: rest, (Cache.intern state.nodes (first :: rest)).1,
      by simpa [construct, ids] using (Cache.intern_correct state.nodes (first :: rest) validNodes).2.1,
      by simp [construct, ids]⟩

theorem canonical_grows (growth : Grows before after) (present : CanonicalNode before reference) : CanonicalNode after reference := by
  rcases present with empty | ⟨key, entry, stored, same⟩
  · exact Or.inl empty
  · exact Or.inr ⟨key, entry, growth.nodeTable key entry stored, same⟩

/-- Equal reads on a finite list give equal decoded row lists. -/
theorem filterMap_congr_on (keys : List Key) (left right : Key → Option Value)
    (same : ∀ key ∈ keys, left key = right key) : keys.filterMap left = keys.filterMap right := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.filterMap_cons, same key (by simp), ih (fun other member => same other (by simp [member]))]

/-- Growing both caches preserves every old canonical node's complete row list. -/
theorem rows_stable (before after : Caches Symbol Guard) (valid : Valid before) (growth : Grows before after)
    (reference : Nat) (present : CanonicalNode before reference) : rows before reference = rows after reference := by
  rcases present with rfl | ⟨key, entry, stored, rfl⟩
  · rfl
  · have issued := (valid.nodes.2 key entry stored).2
    simp only [rows, issued, growth.nodeIssued entry.identity key issued, Option.getD_some]
    apply filterMap_congr_on
    intro identity member
    obtain ⟨edge, canonical, same⟩ := (valid.keys entry.identity key issued).2.2 identity member
    have found := (valid.edges.2 edge.key edge canonical).2
    rw [same] at found
    rw [found, growth.edgeIssued identity edge.key found]

/-- A completed constructor has exact readback after any later cache growth. -/
theorem construct_final_rows [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (before after : Caches Symbol Guard)
    (valid : Valid before) (growth : Grows (construct inputs before).2 after) (edge : EnumerationState.Edge Symbol Guard) :
    edge ∈ rows after (construct inputs before).1 ↔ edge ∈ inputs ∧ 0 ∉ edge.children := by
  rw [← rows_stable (construct inputs before).2 after (construct_valid inputs before valid) growth _
    (construct_canonical inputs before valid.nodes)]
  exact construct_rows inputs before valid.edges valid.nodes edge

/-- A canonical edge appears in decoded rows exactly when its identity is in the node key. -/
theorem canonical_edge_member (state : Cache.State (EnumerationState.Edge Symbol Guard)) (valid : Cache.Valid state)
    (ids : List Nat)
    (known : ∀ identity ∈ ids, ∃ entry, state.table entry.key = some entry ∧ entry.identity = identity)
    (entry : Cache.Interned (EnumerationState.Edge Symbol Guard)) (stored : state.table entry.key = some entry) :
    entry.key ∈ ids.filterMap state.issued ↔ entry.identity ∈ ids := by
  constructor
  · intro present
    obtain ⟨identity, member, issued⟩ := List.mem_filterMap.mp present
    obtain ⟨other, otherStored, otherIdentity⟩ := known identity member
    have otherIssued := (valid.2 other.key other otherStored).2
    rw [otherIdentity] at otherIssued
    have sameKey : other.key = entry.key := Option.some.inj (otherIssued.symm.trans issued)
    have sameId := (Cache.identity_eq_iff_key_eq state valid otherStored stored).mpr sameKey
    rw [← sameId, otherIdentity]
    exact member
  · intro member
    exact List.mem_filterMap.mpr ⟨entry.identity, member, (valid.2 entry.key entry stored).2⟩

/-- Exact decoded row sets determine the underlying canonical edge-identity set. -/
theorem decoded_sets (state : Cache.State (EnumerationState.Edge Symbol Guard)) (valid : Cache.Valid state)
    (left right : List Nat)
    (leftKnown : ∀ identity ∈ left, ∃ entry, state.table entry.key = some entry ∧ entry.identity = identity)
    (rightKnown : ∀ identity ∈ right, ∃ entry, state.table entry.key = some entry ∧ entry.identity = identity)
    (same : ∀ edge, edge ∈ left.filterMap state.issued ↔ edge ∈ right.filterMap state.issued) :
    ∀ identity, identity ∈ left ↔ identity ∈ right := by
  intro identity
  constructor
  · intro member
    obtain ⟨entry, stored, idEq⟩ := leftKnown identity member
    have row := (canonical_edge_member state valid left leftKnown entry stored).mpr (by simpa [idEq] using member)
    simpa [idEq] using (canonical_edge_member state valid right rightKnown entry stored).mp ((same entry.key).mp row)
  · intro member
    obtain ⟨entry, stored, idEq⟩ := rightKnown identity member
    have row := (canonical_edge_member state valid right rightKnown entry stored).mpr (by simpa [idEq] using member)
    simpa [idEq] using (canonical_edge_member state valid left leftKnown entry stored).mp ((same entry.key).mpr row)

/-- Every stored node has at least one readable edge. -/
theorem stored_nonempty (state : Caches Symbol Guard) (valid : Valid state)
    (key : List Nat) (entry : Cache.Interned (List Nat)) (stored : state.nodes.table key = some entry) :
    ∃ edge, edge ∈ rows state (entry.identity + 1) := by
  have issued := (valid.nodes.2 key entry stored).2
  obtain ⟨nonempty, _, present⟩ := valid.keys entry.identity key issued
  cases key with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    obtain ⟨edge, edgeStored, same⟩ := present first (by simp)
    refine ⟨edge.key, ?_⟩
    simp only [rows, issued, Option.getD_some]
    apply (canonical_edge_member state.edges valid.edges _ present edge edgeStored).mpr
    simp [same]

/-- Canonical node identities agree exactly when their decoded row sets agree. -/
theorem nodes_equal_iff (state : Caches Symbol Guard) (valid : Valid state)
    (left right : Nat) (leftCanonical : CanonicalNode state left) (rightCanonical : CanonicalNode state right) :
    left = right ↔ ∀ edge, edge ∈ rows state left ↔ edge ∈ rows state right := by
  constructor
  · intro same
    simp [same]
  · intro same
    rcases leftCanonical with rfl | ⟨leftKey, leftEntry, leftStored, rfl⟩
    · rcases rightCanonical with rfl | ⟨rightKey, rightEntry, rightStored, rfl⟩
      · rfl
      · obtain ⟨edge, member⟩ := stored_nonempty state valid rightKey rightEntry rightStored
        have impossible := (same edge).mpr member
        simp [rows] at impossible
    · rcases rightCanonical with rfl | ⟨rightKey, rightEntry, rightStored, rfl⟩
      · obtain ⟨edge, member⟩ := stored_nonempty state valid leftKey leftEntry leftStored
        have impossible := (same edge).mp member
        simp [rows] at impossible
      · have leftIssued := (valid.nodes.2 leftKey leftEntry leftStored).2
        have rightIssued := (valid.nodes.2 rightKey rightEntry rightStored).2
        obtain ⟨_, leftSorted, leftKnown⟩ := valid.keys leftEntry.identity leftKey leftIssued
        obtain ⟨_, rightSorted, rightKnown⟩ := valid.keys rightEntry.identity rightKey rightIssued
        have rowSets : ∀ edge, edge ∈ leftKey.filterMap state.edges.issued ↔ edge ∈ rightKey.filterMap state.edges.issued := by
          simpa only [rows, leftIssued, rightIssued, Option.getD_some] using same
        have keyEq : leftKey = rightKey := by
          rw [← leftSorted, ← rightSorted]
          exact (canonicalIds_equal _ _).mpr (decoded_sets state.edges valid.edges leftKey rightKey leftKnown rightKnown rowSets)
        exact congrArg (· + 1) ((Cache.identity_eq_iff_key_eq state.nodes valid.nodes leftStored rightStored).mpr keyEq)

/-- Reordering or repeating retained alternatives reuses the same node in one growing cache. -/
theorem construct_same_identity [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (left right : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard) (valid : Valid state)
    (same : ∀ edge, (edge ∈ left ∧ 0 ∉ edge.children) ↔ (edge ∈ right ∧ 0 ∉ edge.children)) :
    (construct left state).1 = (construct right (construct left state).2).1 := by
  let first := construct left state
  let second := construct right first.2
  have firstValid := construct_valid left state valid
  have secondValid := construct_valid right first.2 firstValid
  have growth := construct_grows right first.2 firstValid.edges firstValid.nodes
  apply (nodes_equal_iff second.2 secondValid first.1 second.1
    (canonical_grows growth (construct_canonical left state valid.nodes))
    (construct_canonical right first.2 firstValid.nodes)).mpr
  intro edge
  exact (construct_final_rows left state second.2 valid growth edge).trans
    ((same edge).trans (construct_rows right first.2 firstValid.edges firstValid.nodes edge).symm)

/-- Read decoded rows as the independent guarded constructor automaton. -/
noncomputable def automaton (state : Caches Symbol Guard) (meaning : Guard → Term Symbol → Prop) : Automaton Nat Symbol :=
  fun identity => (rows state identity).map (EnumerationLanguage.edgeView meaning)

/-- Empty-child removal and identity normalization preserve the complete constructor language. -/
theorem construct_language [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (validEdges : Cache.Valid state.edges) (validNodes : Cache.Valid state.nodes)
    (meaning : Guard → Term Symbol → Prop) (term : Term Symbol) :
    Accepts (automaton (construct inputs state).2 meaning) (construct inputs state).1 term ↔
      SymbolicGraph.AcceptsRows (automaton (construct inputs state).2 meaning)
        (inputs.map (EnumerationLanguage.edgeView meaning)) term := by
  cases term with
  | node symbol children =>
    rw [accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, listed, rfl⟩ := List.mem_map.mp member
      have sourceMember := ((construct_rows inputs state validEdges validNodes original).mp listed).1
      exact ⟨EnumerationLanguage.edgeView meaning original, List.mem_map.mpr ⟨original, sourceMember, rfl⟩,
        label, runs, guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      have live : 0 ∉ original.children := by
        intro absent
        obtain ⟨child, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ runs 0 absent
        exact SymbolicGraphView.empty_rows_reject (automaton (construct inputs state).2 meaning) 0 (by simp [automaton, rows]) child accepted
      exact ⟨EnumerationLanguage.edgeView meaning original,
        List.mem_map.mpr ⟨original, (construct_rows inputs state validEdges validNodes original).mpr ⟨sourceMember, live⟩, rfl⟩,
        label, runs, guard⟩

/-- A finite edge-intern pass preserves every checked-key property. -/
theorem internAll_property [DecidableEq Key] (property : Key → Prop) (keys : List Key) (state : Cache.State Key)
    (old : ∀ identity key, state.issued identity = some key → property key)
    (checked : ∀ key ∈ keys, property key) :
    ∀ identity key, (internAll keys state).2.issued identity = some key → property key := by
  induction keys generalizing state with
  | nil => exact old
  | cons first rest ih =>
    exact ih _ (intern_property property state old first (checked first (by simp)))
      (fun key member => checked key (by simp [member]))

/-- Valid input rows preserve edge validity in the concrete edge cache. -/
theorem construct_checked [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (inputs : List (EnumerationState.Edge Symbol Guard)) (state : Caches Symbol Guard)
    (old : ∀ identity edge, state.edges.issued identity = some edge → ValidEdge edge)
    (checked : ∀ edge ∈ inputs, ValidEdge edge) :
    ∀ identity edge, (construct inputs state).2.edges.issued identity = some edge → ValidEdge edge := by
  have result := internAll_property ValidEdge inputs state.edges old checked
  cases ids : canonicalIds ((surviving (internAll inputs state.edges).1).map Cache.Interned.identity) <;>
    simpa [construct, ids] using result

/-- Canonical empty output is exactly the distinguished EmptyNode reference. -/
theorem rows_empty_iff (state : Caches Symbol Guard) (valid : Valid state) (reference : Nat)
    (canonical : CanonicalNode state reference) : rows state reference = [] ↔ reference = 0 := by
  constructor
  · intro empty
    rcases canonical with same | ⟨key, entry, stored, rfl⟩
    · exact same
    · obtain ⟨edge, present⟩ := stored_nonempty state valid key entry stored
      simp [empty] at present
  · rintro rfl
    rfl

end MicroCFTA.EnumerationBuilderCaches
