import MicroCFTA.InternedStoredSubstitution

/-!
# Scoped lookup for the stored substitution adapter

Every prepared lexical slot is in bounds. Canonical identity lookup selects
the exact immutable source record. Closed constants, external replacement
lookups, and nearest local binder references retain their source behavior.
-/
namespace MicroCFTA.InternedStoredSubstitutionScope
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedProvenance
open InternedStoredSubstitution
open InternedBinderProtocol (Reference)

/-- Every original prepared record has an in-bounds slot in a containing context. -/
theorem slot_lt (context : List (Value Symbol Guard)) (value : Value Symbol Guard) (member : value ∈ context) :
    slot context value < context.length :=
  List.findIdx_lt_length_of_exists ⟨value, member, by simp⟩

/-- Canonical identity lookup returns the complete immutable source value. -/
theorem slot_lookup (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state context)
    (member : value ∈ context) : context[slot context value]? = some value := by
  have bound := slot_lt context value member
  have identity : (context[slot context value]'bound).referenceOf = value.referenceOf :=
    beq_iff_eq.mp (List.findIdx_getElem (p := fun candidate : Value Symbol Guard => candidate.referenceOf == value.referenceOf))
  have same := resident_reference_injective state coherent (context[slot context value]'bound) value
    (available _ (List.getElem_mem bound)).resident (available value member).resident identity
  rw [List.getElem?_eq_getElem bound, same]

/-- Closed records never use the external reference replacement map. -/
theorem input_closed (value : Value Symbol Guard) (environment : Environment Symbol Guard) (closed : value.free = []) :
    input environment value = value := by
  cases value <;> simp_all [input, Value.free]

/-- The source closed shortcut is exact, including the absence of cache effects. -/
theorem execute_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (closed : value.free = []) :
    execute value environment state = .done value state := by
  simp only [execute, leaves.eq_def, closed, List.isEmpty_nil, ↓reduceIte, encode.eq_def]
  simp [slot, build, input_closed value environment closed]

/-- A source free-reference plan uses the actual optional replacement or retains its original reference. -/
theorem execute_reference [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute, leaves, Value.free, encode, slot, build, input]

/-- Source child plans retain one output slot for each original child. -/
theorem encodeMany_length (context : List (Value Symbol Guard)) (locals : List Reference) (values : List (Value Symbol Guard)) :
    (encodeMany context locals values).length = values.length := by
  induction values with
  | nil => simp [encodeMany]
  | cons first rest ih => simp [encodeMany, ih]

/-- Source edge declarations retain one output edge for each original edge. -/
theorem encodeEdges_length (context : List (Value Symbol Guard)) (locals : List Reference) (edges : List (EdgeValue Symbol Guard)) :
    (encodeEdges context locals edges).length = edges.length := by
  induction edges with
  | nil => simp [encodeEdges]
  | cons first rest ih => cases first; simp [encodeEdges, ih]

mutual
/-- Every encoded source plan is scoped by its actual local and captured input slots. -/
theorem encode_scoped (context : List (Value Symbol Guard)) (locals : List Reference) (value : Value Symbol Guard)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context) :
    Scoped (locals.length + context.length) (encode context locals value) := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [closed])
    simpa only [Scoped] using Nat.add_lt_add_left (slot_lt context value member) locals.length
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases value with
    | empty => trivial
    | reference name =>
        cases found : locals.findIdx? (· == name) with
        | some index =>
            have bound : index < locals.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
            simpa only [found, Scoped] using Nat.lt_of_lt_of_le bound (Nat.le_add_right locals.length context.length)
        | none =>
            have member := covered (.reference name) (by simp)
            simpa only [found, Scoped] using Nat.add_lt_add_left (slot_lt context _ member) locals.length
    | node entry edges depth free => simpa only [Scoped] using encodeEdges_scoped context locals edges covered
    | union entry values depth free => simpa only [Scoped] using encodeMany_scoped context locals values covered
    | mu entry body depth ordinary =>
        have withinScope := encode_scoped context (.interned entry.identity :: locals) body covered
        simpa only [Scoped, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using withinScope
termination_by sizeOf value

/-- Original ordered child plans share exactly their parent's captured context. -/
theorem encodeMany_scoped (context : List (Value Symbol Guard)) (locals : List Reference) (values : List (Value Symbol Guard))
    (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context) :
    ManyScoped (locals.length + context.length) (encodeMany context locals values) := by
  cases values with
  | nil => simp [encodeMany, ManyScoped]
  | cons first rest =>
      simp only [encodeMany, ManyScoped]
      exact ⟨encode_scoped context locals first (fun leaf member => covered leaf (by simp [manyLeaves, member])),
        encodeMany_scoped context locals rest (fun leaf member => covered leaf (by simp [manyLeaves, member]))⟩
termination_by sizeOf values

/-- Original source edge plans read only actual child and local binder slots. -/
theorem encodeEdges_scoped (context : List (Value Symbol Guard)) (locals : List Reference) (edges : List (EdgeValue Symbol Guard))
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context) :
    EdgesScoped (locals.length + context.length) (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp [encodeEdges, EdgesScoped]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesScoped]
          exact ⟨encodeMany_scoped context locals children (fun leaf member => covered leaf (by simp [edgeLeaves, member])),
            encodeEdges_scoped context locals rest (fun leaf member => covered leaf (by simp [edgeLeaves, member]))⟩
termination_by sizeOf edges
end

/-- The complete stored substitution adapter never needs the lexical out-of-scope fallback. -/
theorem execute_scoped (value : Value Symbol Guard) (environment : Environment Symbol Guard) :
    Scoped ((leaves value).map (input environment)).length (encode (leaves value) [] value) := by
  simpa using encode_scoped (leaves value) [] value (fun _ member => member)

/-- A newly rebuilt binder's own reference resolves to its fresh local slot. -/
theorem encode_local_head (context : List (Value Symbol Guard)) (locals : List Reference) (name : Reference) :
    encode context (name :: locals) (.reference name) = .var 0 := by
  simp [encode, Value.free, List.findIdx?_cons]

/-- A reference to any enclosing source binder selects its nearest actual
local slot and does not read the external replacement map. -/
theorem build_local [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (locals : List Reference) (localValues : List (Value Symbol Guard)) (name : Reference) (index : Nat)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (length : localValues.length = locals.length) (localSlot : locals.findIdx? (· == name) = some index) :
    build (encode context locals (.reference name)) (localValues ++ context.map (input environment)) state =
      .done (localValues[index]?.getD .empty) state := by
  have bound : index < localValues.length := by
    rw [length]
    exact (List.findIdx?_eq_some_iff_findIdx_eq.mp localSlot).1
  simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, localSlot, build]
  rw [List.getElem?_append_left bound]

/-- The closed shortcut inside nested binders selects its original actual captured record. -/
theorem build_closed [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (locals : List Reference) (localValues : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Values state context) (member : value ∈ context)
    (length : localValues.length = locals.length) (closed : value.free = []) :
    build (encode context locals value) (localValues ++ context.map (input environment)) state = .done value state := by
  rw [encode.eq_def]
  simp only [closed, List.isEmpty_nil, ↓reduceIte, build]
  rw [List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left, List.getElem?_map,
    slot_lookup context value state coherent available member]
  simp [input_closed value environment closed]

/-- External references use the source replacement environment below any number of local binders. -/
theorem build_external [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (locals : List Reference) (localValues : List (Value Symbol Guard)) (name : Reference)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Values state context) (member : .reference name ∈ context)
    (length : localValues.length = locals.length) (external : locals.findIdx? (· == name) = none) :
    build (encode context locals (.reference name)) (localValues ++ context.map (input environment)) state =
      .done ((environment name).getD (.reference name)) state := by
  simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, external, build]
  rw [List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left, List.getElem?_map,
    slot_lookup context (.reference name) state coherent available member]
  simp [input]

end MicroCFTA.InternedStoredSubstitutionScope
