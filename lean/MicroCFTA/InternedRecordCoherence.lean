import MicroCFTA.InternedConstructorTemplates

/-!
# Canonical record coherence from constructor traces

The two identity caches and the two payload tables start empty. Generated
constructor requests retain the same keys in both representations. Completed
records also retain the source child identities and metadata equations.
-/
namespace MicroCFTA.InternedRecordCoherence
open Cache InternedBinderProtocol InternedConstructorTemplates

/-- An edge payload retains its complete key and ordered child identities. -/
def EdgeFields (key : EdgeKey Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  edge.entry.key = key ∧ edge.children.map Value.referenceOf = key.children

/-- Each node payload has the fields used to construct its actual cache key. -/
def NodeFields (key : NodeKey) (entry : Interned NodeKey) : Value Symbol Guard → Prop
  | .node actual edges depth free =>
      actual = entry ∧ key = .node (edges.map (fun edge => edge.entry.identity)) ∧
        depth = maximumDepth (edges.flatMap EdgeValue.children) ∧
        free = childFree (edges.flatMap EdgeValue.children)
  | .union actual members depth free =>
      actual = entry ∧ key = .union (members.map Value.referenceOf) ∧
        depth = maximumDepth members ∧ free = childFree members
  | .mu actual _ depthShape ordinaryShape =>
      actual = entry ∧ key = muKey depthShape ordinaryShape
  | .empty | .reference _ => False

/-- Stored payloads agree with canonical entries and their constructor fields. -/
structure Coherent (state : InternedConstructorTemplates.State Symbol Guard) : Prop where
  valid : InternedConstructorTemplates.Valid state
  edges : ∀ key value, state.edgeRecords key = some value →
    state.edges.table key = some value.entry ∧ EdgeFields key value
  nodes : ∀ key value, state.nodeRecords key = some value →
    ∃ entry, state.nodes.table key = some entry ∧ NodeFields key entry value

/-- Every completed identity request has a payload. Listed Mu keys may still be pending. -/
structure Covered (pending : List NodeKey) (state : InternedConstructorTemplates.State Symbol Guard) : Prop where
  edges : ∀ key entry, state.edges.table key = some entry → ∃ value, state.edgeRecords key = some value
  nodes : ∀ key entry, state.nodes.table key = some entry →
    key ∈ pending ∨ ∃ value, state.nodeRecords key = some value

/-- Both representations are coherent and complete in the empty state. -/
theorem empty_correct : Coherent (empty (Symbol := Symbol) (Guard := Guard)) ∧
    Covered [] (empty (Symbol := Symbol) (Guard := Guard)) := by
  constructor
  · refine ⟨empty_valid, ?_, ?_⟩ <;> intro key value impossible <;> cases impossible
  · constructor <;> intro key entry impossible <;> cases impossible

/-- An intern operation can only retain an old entry or install its requested entry. -/
theorem intern_cases [DecidableEq Key] (state : Cache.State Key) (key other : Key)
    (entry : Interned Key) (present : (Cache.intern state key).2.table other = some entry) :
    state.table other = some entry ∨ other = key ∧ entry = (Cache.intern state key).1 := by
  cases found : state.table key with
  | some value => exact Or.inl (by simpa [Cache.intern, found] using present)
  | none =>
      by_cases same : other = key
      · subst other
        right
        simpa [Cache.intern, found, install, reserve, keepFirst, put] using present.symm
      · exact Or.inl (by simpa [Cache.intern, found, install, reserve, keepFirst, put, same] using present)

/-- A first-writer payload update contains an old record or its new candidate. -/
theorem record_cases [DecidableEq Key] (table : Table Key Record) (key other : Key)
    (candidate value : Record) (present : keepFirst table key candidate other = some value) :
    table other = some value ∨ other = key ∧ value = candidate := by
  cases found : table key with
  | some existing => exact Or.inl (by simpa [keepFirst, found] using present)
  | none =>
      by_cases same : other = key
      · subst other
        right
        simpa [keepFirst, found, put] using present.symm
      · exact Or.inl (by simpa [keepFirst, found, put, same] using present)

/-- Complete edge fields follow from the constructor callback, not from a cache assumption. -/
theorem edgeStep_coherent [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (fields : ∀ entry, entry.key = key → (identify entry).entry = entry ∧ EdgeFields key (identify entry)) :
    Coherent (edgeStep key identify state).2 := by
  have step := edgeStep_correct key identify state coherent.valid
  have interned := Cache.intern_correct state.edges key coherent.valid.1
  refine ⟨step.1, ?_, ?_⟩
  · intro other value present
    rcases record_cases _ key other _ value present with old | ⟨same, valueEq⟩
    · have original := coherent.edges other value old
      exact ⟨step.2.1.edges _ _ original.1, original.2⟩
    · subst other value
      have actual := fields _ interned.2.2
      refine ⟨?_, actual.2⟩
      rw [actual.1]
      exact interned.2.1
  · intro other value present
    obtain ⟨entry, stored, fields⟩ := coherent.nodes other value present
    exact ⟨entry, stored, fields⟩

/-- Complete node fields follow from the generated identification callback. -/
theorem nodeStep_coherent (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (fields : ∀ entry, entry.key = key → NodeFields key entry (identify entry)) :
    Coherent (nodeStep key identify state).2 := by
  have step := nodeStep_correct key identify state coherent.valid
  have interned := Cache.intern_correct state.nodes key coherent.valid.2
  refine ⟨step.1, ?_, ?_⟩
  · intro other value present
    exact coherent.edges other value present
  · intro other value present
    rcases record_cases _ key other _ value present with old | ⟨same, valueEq⟩
    · obtain ⟨entry, stored, fields⟩ := coherent.nodes other value old
      exact ⟨entry, step.2.1.nodes _ _ stored, fields⟩
    · subst other value
      exact ⟨_, interned.2.1, fields _ interned.2.2⟩

/-- Every edge step supplies a payload for its only new identity entry. -/
theorem edgeStep_covered [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (covered : Covered pending state) : Covered pending (edgeStep key identify state).2 := by
  have step := edgeStep_correct key identify state valid
  constructor
  · intro other entry present
    rcases intern_cases state.edges key other entry present with old | ⟨same, _⟩
    · obtain ⟨value, stored⟩ := covered.edges other entry old
      exact ⟨value, step.2.1.edgeRecords _ _ stored⟩
    · subst other
      exact ⟨_, step.2.2⟩
  · exact covered.nodes

/-- Every node step completes its only new identity entry. -/
theorem nodeStep_covered (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (covered : Covered pending state) : Covered pending (nodeStep key identify state).2 := by
  have step := nodeStep_correct key identify state valid
  constructor
  · exact covered.edges
  · intro other entry present
    rcases intern_cases state.nodes key other entry present with old | ⟨same, _⟩
    · rcases covered.nodes other entry old with delayed | ⟨value, stored⟩
      · exact Or.inl delayed
      · exact Or.inr ⟨value, step.2.1.nodeRecords _ _ stored⟩
    · subst other
      exact Or.inr ⟨_, step.2.2⟩

/-- Each generated effect uses the actual fields of its requested constructor. -/
def Safe (work : InternedConstructorTemplates.Work Symbol Guard Result) : Prop :=
  match work with
  | .pure _ => True
  | .edge key identify resume =>
      (∀ entry, entry.key = key → (identify entry).entry = entry ∧ EdgeFields key (identify entry)) ∧
      ∀ value, Safe (resume value)
  | .node key identify resume =>
      (∀ entry, entry.key = key → NodeFields key entry (identify entry)) ∧ ∀ value, Safe (resume value)

/-- Sequencing preserves constructor-field certification. -/
theorem safe_bind (work : InternedConstructorTemplates.Work Symbol Guard First)
    (next : First → InternedConstructorTemplates.Work Symbol Guard Result)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work.bind next) := by
  induction work with
  | pure value => exact later value
  | edge key identify resume ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩
  | node key identify resume ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩

/-- Certified constructor effects preserve all completed payloads and pending slots. -/
theorem run_correct [DecidableEq (EdgeKey Symbol Guard)]
    (work : InternedConstructorTemplates.Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) (safe : Safe work)
    (coherent : Coherent state) (covered : Covered pending state) :
    Coherent (run work state).2 ∧ Covered pending (run work state).2 := by
  induction work generalizing state with
  | pure value => exact ⟨coherent, covered⟩
  | edge key identify resume ih =>
      exact ih _ _ (safe.2 _) (edgeStep_coherent _ _ _ coherent safe.1)
        (edgeStep_covered _ _ _ coherent.valid covered)
  | node key identify resume ih =>
      exact ih _ _ (safe.2 _) (nodeStep_coherent _ _ _ coherent safe.1)
        (nodeStep_covered _ _ _ coherent.valid covered)

/-- Ordered edge identities and child references are taken from the actual child records. -/
theorem makeEdge_safe (symbol : Symbol) (constraint : Guard) (children : List (Value Symbol Guard)) :
    Safe (makeEdge symbol constraint children) := by
  exact ⟨fun _ found => ⟨rfl, found, rfl⟩, fun _ => trivial⟩

/-- Smart-node normalization supplies the exact canonical edge list and metadata. -/
theorem makeNode_safe (edges : List (EdgeValue Symbol Guard)) : Safe (makeNode edges) := by
  unfold makeNode
  dsimp only
  split
  · trivial
  · exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => trivial⟩

/-- Every union branch returns an existing record or supplies exact constructor fields. -/
theorem makeUnion_safe (values : List (Value Symbol Guard)) : Safe (makeUnion values) := by
  unfold makeUnion
  split
  · trivial
  · trivial
  · split
    · exact makeNode_safe _
    · exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => trivial⟩

mutual
/-- Template syntax derives constructor-field certification for every generated request. -/
theorem compile_safe (template : Template Symbol Guard) (argument : Value Symbol Guard) :
    Safe (compile template argument) := by
  cases template <;> simp only [compile]
  case argument => trivial
  case captured => trivial
  case node edges => exact safe_bind _ _ (compileEdges_safe edges argument) makeNode_safe
  case union members => exact safe_bind _ _ (compileMany_safe members argument) makeUnion_safe
termination_by sizeOf template

/-- Child compilation certifies each effect in source order. -/
theorem compileMany_safe (templates : List (Template Symbol Guard)) (argument : Value Symbol Guard) :
    Safe (compileMany templates argument) := by
  cases templates <;> simp only [compileMany]
  case nil => trivial
  case cons first rest =>
      exact safe_bind _ _ (compile_safe first argument) (fun _ =>
        safe_bind _ _ (compileMany_safe rest argument) (fun _ => trivial))
termination_by sizeOf templates

/-- Each generated edge certifies its fields after its children have completed. -/
theorem compileEdges_safe (templates : List (EdgeTemplate Symbol Guard)) (argument : Value Symbol Guard) :
    Safe (compileEdges templates argument) := by
  cases templates with
  | nil => simp [compileEdges, Safe]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [compileEdges]
          exact safe_bind _ _ (compileMany_safe children argument) (fun _ =>
            safe_bind _ _ (makeEdge_safe _ _ _) (fun _ =>
              safe_bind _ _ (compileEdges_safe rest argument) (fun _ => trivial)))
termination_by sizeOf templates
end

/-- Actual template compilation preserves global key-to-record coherence and completion. -/
theorem compile_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (argument : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (covered : Covered pending state) :
    Coherent (run (compile template argument) state).2 ∧ Covered pending (run (compile template argument) state).2 :=
  run_correct _ _ (compile_safe template argument) coherent covered

/-- Reserving a Mu identity adds one explicit pending slot and preserves all existing records. -/
theorem reserve_correct (key : NodeKey) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (covered : Covered pending state) :
    let allocated := {state with nodes := (Cache.intern state.nodes key).2}
    Coherent allocated ∧ Covered (key :: pending) allocated := by
  have entry := Cache.intern_correct state.nodes key coherent.valid.2
  have growth := InternedBinderProtocol.intern_grows state.nodes key
  constructor
  · refine ⟨⟨coherent.valid.1, entry.1⟩, coherent.edges, ?_⟩
    intro other value present
    obtain ⟨original, stored, fields⟩ := coherent.nodes other value present
    exact ⟨original, growth _ _ stored, fields⟩
  · refine ⟨covered.edges, ?_⟩
    intro other value present
    rcases intern_cases state.nodes key other value present with old | ⟨same, _⟩
    · rcases covered.nodes other value old with delayed | ready
      · exact Or.inl (by simp [delayed])
      · exact Or.inr ready
    · exact Or.inl (by simp [same])

/-- Completing one reserved key removes its pending exception and retains the first complete payload. -/
theorem complete_correct (key : NodeKey) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered (key :: pending) state) (stored : state.nodes.table key = some entry)
    (fields : NodeFields key entry value) :
    let completed := {state with nodeRecords := keepFirst state.nodeRecords key value}
    Coherent completed ∧ Covered pending completed := by
  constructor
  · refine ⟨coherent.valid, coherent.edges, ?_⟩
    intro other record present
    rcases record_cases _ key other value record present with old | ⟨same, valueEq⟩
    · exact coherent.nodes other record old
    · subst other record
      exact ⟨entry, stored, fields⟩
  · refine ⟨covered.edges, ?_⟩
    intro other actual present
    by_cases same : other = key
    · subst other
      exact Or.inr (keepFirst_present state.nodeRecords key value)
    · rcases covered.nodes other actual present with delayed | ⟨record, original⟩
      · exact Or.inl (by simpa [same] using delayed)
      · exact Or.inr ⟨record, keepFirst_extends _ _ _ _ _ original⟩

/-- Both source probes preserve complete key-to-record correspondence. -/
theorem probes_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered pending state) :
    Coherent (probes template state).2 ∧ Covered pending (probes template state).2 := by
  have first := compile_correct template (.reference .depth) state coherent covered
  exact compile_correct template
    (.reference (.uninterned (run (compile template (.reference .depth)) state).1.depth)) _ first.1 first.2

/-- Actual Mu completion retains its probe key, canonical identity, and complete body record. -/
theorem finishMu_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (covered : Covered pending state) :
    Coherent (finishMu template depthShape ordinaryShape state).2 ∧
      Covered pending (finishMu template depthShape ordinaryShape state).2 := by
  cases found : state.nodeRecords (muKey depthShape ordinaryShape) with
  | some value => simpa [finishMu, found] using And.intro coherent covered
  | none =>
      let entry := Cache.intern state.nodes (muKey depthShape ordinaryShape)
      let allocated := {state with nodes := entry.2}
      let body := run (compile template (.reference (.interned entry.1.identity))) allocated
      have reserved := reserve_correct (muKey depthShape ordinaryShape) state coherent covered
      have built := compile_correct template (.reference (.interned entry.1.identity)) allocated reserved.1 reserved.2
      have grown := (InternedConstructorTemplates.run_correct
        (compile template (.reference (.interned entry.1.identity))) allocated reserved.1.valid).2
      have stored : body.2.nodes.table (muKey depthShape ordinaryShape) = some entry.1 :=
        grown.nodes _ _ (Cache.intern_correct _ _ coherent.valid.2).2.1
      have completed := complete_correct (muKey depthShape ordinaryShape) entry.1
        (.mu entry.1 body.1 depthShape ordinaryShape) body.2 built.1 built.2 stored ⟨rfl, rfl⟩
      simpa only [finishMu, found] using completed

/-- All generated source Mu requests preserve coherence without a supplied cache invariant. -/
theorem internMu_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered pending state) :
    Coherent (internMu template state).2 ∧ Covered pending (internMu template state).2 := by
  have checked := probes_correct template state coherent covered
  exact finishMu_correct template _ _ _ checked.1 checked.2

/-- Smart Mu cleanup changes the result only; both cache representations remain complete. -/
theorem createMu_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (covered : Covered pending state) :
    Coherent (createMu template state).2 ∧ Covered pending (createMu template state).2 :=
  internMu_correct template state coherent covered

/-- A finite source construction trace starts empty and executes generated ordinary or Mu templates. -/
inductive Constructed [DecidableEq (EdgeKey Symbol Guard)] : InternedConstructorTemplates.State Symbol Guard → Prop
  | empty : Constructed empty
  | ordinary (before : Constructed state) (template : Template Symbol Guard) (argument : Value Symbol Guard) :
      Constructed (run (compile template argument) state).2
  | binder (before : Constructed state) (template : Template Symbol Guard) :
      Constructed (createMu template state).2

/-- Empty-cache construction traces derive the complete global record invariant. -/
theorem constructed_correct [DecidableEq (EdgeKey Symbol Guard)]
    {state : InternedConstructorTemplates.State Symbol Guard}
    (built : Constructed state) : Coherent state ∧ Covered [] state := by
  induction built with
  | empty => exact empty_correct
  | ordinary before template argument ih => exact compile_correct template argument _ ih.1 ih.2
  | binder before template ih => exact createMu_correct template _ ih.1 ih.2

/-- Each completed canonical node entry has a payload with that exact entry and constructor fields. -/
theorem node_readback [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state)
    (key : NodeKey) (entry : Interned NodeKey) (present : state.nodes.table key = some entry) :
    ∃ value, state.nodeRecords key = some value ∧ NodeFields key entry value := by
  have correct := constructed_correct built
  have covered := correct.2.nodes key entry present
  simp only [List.not_mem_nil, false_or] at covered
  obtain ⟨value, stored⟩ := covered
  obtain ⟨actual, found, fields⟩ := correct.1.nodes key value stored
  have same : actual = entry := Option.some.inj (found.symm.trans present)
  exact ⟨value, stored, same ▸ fields⟩

/-- Each completed canonical edge entry has its exact payload and ordered child identities. -/
theorem edge_readback [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state)
    (key : EdgeKey Symbol Guard) (entry : Interned (EdgeKey Symbol Guard))
    (present : state.edges.table key = some entry) :
    ∃ value, state.edgeRecords key = some value ∧ value.entry = entry ∧ EdgeFields key value := by
  have correct := constructed_correct built
  obtain ⟨value, stored⟩ := correct.2.edges key entry present
  have record := correct.1.edges key value stored
  exact ⟨value, stored, Option.some.inj (record.1.symm.trans present), record.2⟩

/-- A finite inventory reads complete node records from the actual issued identity supply. -/
def nodeInventory (state : InternedConstructorTemplates.State Symbol Guard) : List (Value Symbol Guard) :=
  (List.range state.nodes.next).filterMap fun identity => (state.nodes.issued identity).bind state.nodeRecords

/-- Every completed node record belongs to the finite inventory derived from its actual counter. -/
theorem node_inventory_complete [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state)
    (key : NodeKey) (value : Value Symbol Guard) (stored : state.nodeRecords key = some value) :
    value ∈ nodeInventory state := by
  have coherent := (constructed_correct built).1
  obtain ⟨entry, present, _⟩ := coherent.nodes key value stored
  have issued := (coherent.valid.2.2 key entry present).2
  have bound := coherent.valid.2.1 entry.identity key issued
  exact List.mem_filterMap.mpr ⟨entry.identity, List.mem_range.mpr bound, by simp [issued, stored]⟩

/-- The concrete inventory has at most one position per issued identity. -/
theorem node_inventory_bound (state : InternedConstructorTemplates.State Symbol Guard) :
    (nodeInventory state).length ≤ state.nodes.next := by
  simpa [nodeInventory] using List.length_filterMap_le
    (fun identity => (state.nodes.issued identity).bind state.nodeRecords) (List.range state.nodes.next)

/-- Read the canonical entry carried by a stored node constructor. -/
def entryOf : Value Symbol Guard → Option (Interned NodeKey)
  | .node entry _ _ _ | .union entry _ _ _ | .mu entry _ _ _ => some entry
  | .empty | .reference _ => none

/-- Constructor-field agreement fixes the complete entry carried by the record. -/
theorem fields_entry (key : NodeKey) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields key entry value) : entryOf value = some entry := by
  cases value <;> simp_all [NodeFields, entryOf]

/-- Equal issued identities of two stored node records imply equality of the complete payloads. -/
theorem node_identity_unique [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state)
    (leftKey rightKey : NodeKey) (left right : Value Symbol Guard)
    (leftStored : state.nodeRecords leftKey = some left) (rightStored : state.nodeRecords rightKey = some right)
    (leftEntry rightEntry : Interned NodeKey) (leftField : entryOf left = some leftEntry)
    (rightField : entryOf right = some rightEntry) (same : leftEntry.identity = rightEntry.identity) : left = right := by
  have coherent := (constructed_correct built).1
  obtain ⟨first, firstStored, firstFields⟩ := coherent.nodes leftKey left leftStored
  obtain ⟨second, secondStored, secondFields⟩ := coherent.nodes rightKey right rightStored
  have firstEq : first = leftEntry := Option.some.inj ((fields_entry _ _ _ firstFields).symm.trans leftField)
  have secondEq : second = rightEntry := Option.some.inj ((fields_entry _ _ _ secondFields).symm.trans rightField)
  subst first second
  have keys := (Cache.identity_eq_iff_key_eq state.nodes coherent.valid.2 firstStored secondStored).mp same
  subst rightKey
  exact Option.some.inj (leftStored.symm.trans rightStored)

/-- The finite inventory contains exactly the completed node records. -/
theorem node_inventory_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (built : Constructed state)
    (value : Value Symbol Guard) : value ∈ nodeInventory state ↔ ∃ key, state.nodeRecords key = some value := by
  constructor
  · intro member
    obtain ⟨identity, _, present⟩ := List.mem_filterMap.mp member
    cases issued : state.nodes.issued identity with
    | none => simp [issued] at present
    | some key => exact ⟨key, by simpa [issued] using present⟩
  · rintro ⟨key, stored⟩
    exact node_inventory_complete state built key value stored

/-- The raw Mu record is in the constructed state's finite inventory even if cleanup removes the binder. -/
theorem mu_inventory_member [DecidableEq (EdgeKey Symbol Guard)]
    (template : Template Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (built : Constructed state) : (internMu template state).1 ∈ nodeInventory (createMu template state).2 := by
  have later : Constructed (createMu template state).2 := .binder built template
  apply node_inventory_complete _ later (muKey (probes template state).1.1 (probes template state).1.2)
  exact finishMu_stored template _ _ _

end MicroCFTA.InternedRecordCoherence
