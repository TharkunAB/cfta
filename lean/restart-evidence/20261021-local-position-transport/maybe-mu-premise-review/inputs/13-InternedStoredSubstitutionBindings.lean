import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.InternedNestedDependencies

/-!
# Source free-binding restriction for stored substitution

Prepared execution reads only bindings of the original record's free
names. Local binder names shadow external replacements. Restricting an
environment to the source cached free set therefore preserves the complete
constructor computation, including cache effects and pending outcomes.
-/
namespace MicroCFTA.InternedStoredSubstitutionBindings
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedDependencies
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedNormalizationFree
open InternedBinderProtocol (Reference)

/-- Agreement is required only for free names not bound by the current lexical prefix. -/
def AgreeFree (locals : List Reference) (value : Value Symbol Guard)
    (first second : Environment Symbol Guard) : Prop :=
  ∀ name ∈ value.free, name ∉ locals → first name = second name

/-- An actual global slot contains the original constant or the supplied free-reference replacement. -/
theorem global_lookup (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state context)
    (member : value ∈ context) (length : localValues.length = locals.length) :
    (localValues ++ context.map (input environment))[locals.length + slot context value]? = some (input environment value) := by
  rw [List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left, List.getElem?_map,
    slot_lookup context value state coherent available member]
  rfl

mutual
/-- Cached source free metadata suffices for equality at every lexical slot
read by the prepared record, without assuming an output or key equation. -/
theorem encode_agree (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (contextAvailable : Values state context) (available : Available state value)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context) (length : localValues.length = locals.length)
    (agree : AgreeFree locals value first second) :
    Agree (inputs (encode context locals value)) (localValues ++ context.map (input first))
      (localValues ++ context.map (input second)) := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [closed])
    intro index present
    have same : index = locals.length + slot context value := by simpa only [inputs, List.mem_singleton] using present
    subst index
    rw [global_lookup context locals localValues value first state coherent contextAvailable member length,
      global_lookup context locals localValues value second state coherent contextAvailable member length]
    simp only [Option.getD_some, input_closed value first (List.isEmpty_iff.mp closed),
      input_closed value second (List.isEmpty_iff.mp closed)]
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases value with
    | empty => simp [Agree, inputs]
    | reference name =>
        cases found : locals.findIdx? (· == name) with
        | some index =>
            intro selected present
            have same : selected = index := by simpa only [found, inputs, List.mem_singleton] using present
            subst selected
            have bound : index < localValues.length := by
              rw [length]
              exact (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
            rw [List.getElem?_append_left bound, List.getElem?_append_left bound]
        | none =>
            intro selected present
            have same : selected = locals.length + slot context (.reference name) := by simpa only [found, inputs, List.mem_singleton] using present
            subst selected
            have member := covered (.reference name) (by simp)
            have external : name ∉ locals := by
              intro present
              have impossible := (List.findIdx?_eq_none_iff.mp found) name present
              simp at impossible
            have equal := agree name (by simp [Value.free]) external
            rw [global_lookup context locals localValues (.reference name) first state coherent contextAvailable member length,
              global_lookup context locals localValues (.reference name) second state coherent contextAvailable member length]
            simp [input, equal]
    | node entry edges depth free =>
        have childrenAgree : ∀ child ∈ edges.flatMap EdgeValue.children, AgreeFree locals child first second := by
          intro child member name named external
          apply agree name _ external
          simp only [Value.free, node_free state coherent entry edges depth free available.resident]
          exact (childFree_member _ name).mpr ⟨child, member, named⟩
        simpa only [inputs] using encodeEdges_agree context locals localValues edges first second state coherent contextAvailable
          (fun child member => available.children child member) covered length childrenAgree
    | union entry members depth free =>
        have childrenAgree : ∀ child ∈ members, AgreeFree locals child first second := by
          intro child member name named external
          apply agree name _ external
          simp only [Value.free, union_free state coherent entry members depth free available.resident]
          exact (childFree_member _ name).mpr ⟨child, member, named⟩
        simpa only [inputs] using encodeMany_agree context locals localValues members first second state coherent contextAvailable
          (fun child member => available.children child member) covered length childrenAgree
    | mu entry body depth ordinary =>
        have bodyAgree : AgreeFree (.interned entry.identity :: locals) body first second := by
          intro name named external
          have different : name ≠ .interned entry.identity := fun same => external (by simp [same])
          exact agree name (by simp [Value.free, named, different]) (fun member => external (by simp [member]))
        have inner := encode_agree context (.interned entry.identity :: locals) (.empty :: localValues) body
          first second state coherent contextAvailable (available.children body (by simp [InternedProbeProvenance.children]))
          covered (by simp [length]) bodyAgree
        intro index present
        simp only [inputs] at present
        obtain ⟨source, included, result⟩ := List.mem_filterMap.mp present
        cases source with
        | zero => simp [enclosing] at result
        | succ source =>
            have same : source = index := by simpa [enclosing] using result
            subst index
            exact inner (source + 1) included
termination_by sizeOf value

/-- Ordered child free sets determine all external input slots of their prepared plans. -/
theorem encodeMany_agree (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (contextAvailable : Values state context) (available : Values state values)
    (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context) (length : localValues.length = locals.length)
    (agree : ∀ value ∈ values, AgreeFree locals value first second) :
    Agree (manyInputs (encodeMany context locals values)) (localValues ++ context.map (input first))
      (localValues ++ context.map (input second)) := by
  cases values with
  | nil => simp [Agree, encodeMany, manyInputs]
  | cons head tail =>
      intro index member
      simp only [encodeMany, manyInputs] at member
      rcases List.mem_append.mp member with left | right
      · exact encode_agree context locals localValues head first second state coherent contextAvailable (available head (by simp))
          (fun leaf member => covered leaf (by simp [manyLeaves, member])) length (agree head (by simp)) index left
      · exact encodeMany_agree context locals localValues tail first second state coherent contextAvailable
          (fun value member => available value (by simp [member]))
          (fun leaf member => covered leaf (by simp [manyLeaves, member])) length
          (fun value member => agree value (by simp [member])) index right
termination_by sizeOf values

/-- Original edge symbols and guards do not add environment dependencies. -/
theorem encodeEdges_agree (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (contextAvailable : Values state context)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context) (length : localValues.length = locals.length)
    (agree : ∀ value ∈ edges.flatMap EdgeValue.children, AgreeFree locals value first second) :
    Agree (edgeInputs (encodeEdges context locals edges)) (localValues ++ context.map (input first))
      (localValues ++ context.map (input second)) := by
  cases edges with
  | nil => simp [Agree, encodeEdges, edgeInputs]
  | cons head tail =>
      cases head with
      | mk entry children =>
          intro index member
          simp only [encodeEdges, edgeInputs] at member
          rcases List.mem_append.mp member with left | right
          · exact encodeMany_agree context locals localValues children first second state coherent contextAvailable
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) length
              (fun value member => agree value (by simp [EdgeValue.children, member])) index left
          · exact encodeEdges_agree context locals localValues tail first second state coherent contextAvailable
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) length
              (fun value member => agree value (by simp [EdgeValue.children, member])) index right
termination_by sizeOf edges
end

/-- Only the original stored free bindings can change the complete prepared execution. -/
theorem execute_congr [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value)
    (agree : ∀ name ∈ value.free, first name = second name) : execute value first state = execute value second state := by
  apply build_congr
  simpa only [List.nil_append] using encode_agree (leaves value) [] [] value first second state coherent
    (leaves_available value state available) available (fun _ member => member) rfl (fun name member _ => agree name member)

/-- The source restriction to an open Mu's cached free set preserves the exact computation. -/
theorem execute_restrict [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    execute value (fun name => if name ∈ value.free then environment name else none) state = execute value environment state := by
  apply execute_congr value _ environment state coherent available
  intro name member
  simp [member]

end MicroCFTA.InternedStoredSubstitutionBindings
