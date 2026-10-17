import MicroCFTA.SourceRecursiveIntersectionInputExact
import MicroCFTA.InternedValueMassHeap

/-!
# Computable structural mass bounds for recursive source inputs

Actual tagged payload reads determine the mass. Mu includes its body and
both stored probes. Empty defaults and references have unit mass.
This mass supplies an alternative to the metadata-sensitive payload rank.
Closed reference reachability uses the same finite original-input interface.
No completed intersection or future output bound is assumed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMassInputBounds
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule
open SourceRecursiveIntersectionInputView
variable {Symbol Guard : Type}

/-- Count the complete payload selected by the actual source input tag. -/
def mass (state : State Symbol Guard) (input : Input) : Nat :=
  InternedValueMass.value (payload state input)

/-- Complete available inputs read back their exact structural mass. -/
theorem mass_readback (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    mass state input = InternedValueMass.value value :=
  congrArg InternedValueMass.value (payload_readback state facts value available input complete)

/-- Unsupported references map to unit-mass Empty without increasing mass. -/
theorem mass_le (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) :
    mass state (inputOf value) ≤ InternedValueMass.value value := by
  cases value with
  | empty => exact Nat.le_refl _
  | reference name =>
      cases name <;> simp [mass, payload, inputOf, IntersectionFlatMemoKey.input, Value.referenceOf, InternedValueMass.value]
  | node entry rows depth free | union entry rows depth free | mu entry rows depth free =>
      exact Nat.le_of_eq (mass_readback state facts _ available _ rfl)

/-- Every selected payload has positive mass, including Empty defaults. -/
theorem mass_pos (state : State Symbol Guard) (input : Input) : 0 < mass state input :=
  InternedValueMass.value_pos _

private theorem actual_body_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (available : Available state (.mu entry body depth ordinary)) :
    mass state ((view state holds).body entry.identity) < mass state (.mu entry.identity) := by
  have selected := payload_readback state facts _ available (.mu entry.identity) rfl
  have bodyExact : (view state holds).body entry.identity = inputOf body := by simp only [view, selected]
  rw [bodyExact, mass_readback state facts _ available _ rfl]
  exact Nat.lt_of_le_of_lt (mass_le state facts body (available.children body (by simp [children])))
    (InternedValueMass.mu_body_lt entry body depth ordinary)

/-- An original Mu input strictly contains the body returned by its actual source read. -/
theorem body_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.mu name)) :
    mass state ((view state holds).body name) < mass state (.mu name) := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete
  case mu entry body depth ordinary original =>
    cases complete
    exact actual_body_mass state facts holds entry body depth ordinary available

private theorem actual_row_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.node entry edges depth free))
    (selectedRow : Row Symbol) (present : selectedRow ∈ (view state holds).rows entry.identity)
    (input : Input) (member : input ∈ selectedRow.children) :
    mass state input < mass state (.node entry.identity) := by
  have selected := payload_readback state facts _ available (.node entry.identity) rfl
  have rowsExact : (view state holds).rows entry.identity = edges.map (row holds) := by simp only [view, selected]
  rw [rowsExact] at present
  obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
  obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp member
  rw [mass_readback state facts _ available _ rfl]
  exact Nat.lt_of_le_of_lt
    (mass_le state facts child (available.children child (List.mem_flatMap.mpr ⟨edge, inEdges, inChildren⟩)))
    (InternedValueMass.node_child_lt entry edges depth free edge inEdges child inChildren)

private theorem actual_member_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.union entry members depth free))
    (input : Input) (member : input ∈ (view state holds).members entry.identity) :
    mass state input < mass state (.union entry.identity) := by
  have selected := payload_readback state facts _ available (.union entry.identity) rfl
  have membersExact : (view state holds).members entry.identity = members.map inputOf := by simp only [view, selected]
  rw [membersExact] at member
  obtain ⟨child, inMembers, rfl⟩ := List.mem_map.mp member
  rw [mass_readback state facts _ available _ rfl]
  exact Nat.lt_of_le_of_lt (mass_le state facts child (available.children child inMembers))
    (InternedValueMass.union_member_lt entry members depth free child inMembers)

/-- Every actual row child has less mass than its tagged source node. -/
theorem rows_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (identity : Nat) (selectedRow : Row Symbol)
    (present : selectedRow ∈ (view state holds).rows identity) (input : Input) (member : input ∈ selectedRow.children) :
    mass state input < mass state (.node identity) := by
  rcases payload_selected state identity (.node identity) (.inl rfl) with absent | ⟨value, found, same, selected⟩
  · simp [view, absent] at present
  · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.getD_some, reduceCtorEq, Input.node.injEq] at same <;> try contradiction
    case reference reference => cases reference <;> contradiction
    case node entry edges depth free =>
      subst identity
      exact actual_row_mass state facts holds entry edges depth free
        (SourcePreparedSharedRows.read_available state facts _ _ found) selectedRow present input member

/-- Every actual union member has less mass than its tagged source union. -/
theorem members_mass (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (identity : Nat) (input : Input)
    (member : input ∈ (view state holds).members identity) : mass state input < mass state (.union identity) := by
  rcases payload_selected state identity (.union identity) (.inr (.inr rfl)) with absent | ⟨value, found, same, selected⟩
  · simp [view, absent] at member
  · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.getD_some, reduceCtorEq, Input.union.injEq] at same <;> try contradiction
    case reference reference => cases reference <;> contradiction
    case union entry members depth free =>
      subst identity
      exact actual_member_mass state facts holds entry members depth free
        (SourcePreparedSharedRows.read_available state facts _ _ found) input member

/-- The local measure stops at Mu and uses unit mass at references. -/
def localWeight (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) : LocalWeight (view state holds) :=
  structuralLocalWeight (view state holds) (mass state)
    (fun name => mass_pos state (.ref name)) (fun name => mass_pos state (.node name))
    (rows_mass state facts holds) (members_mass state facts holds)

/-- Original closed roots retain the existing finite model with a computable mass rank. -/
def mass_inputBounds (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true) :
    InputBounds (view state holds) (finiteInput state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed) :=
  structuralInputBounds (view state holds)
    (finiteInput state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed)
    (free_correct state facts holds) (inputPairs (inventory state))
    (fun left right leftValid rightValid _ _ => input_pair_mem (inventory state) left right
      ((reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed left leftValid).inventory state facts left)
      ((reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed right rightValid).inventory state facts right))
    (localWeight state facts holds) (mass state)
    (fun name valid => body_mass state facts holds name
      (reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed (.mu name) valid))
    (fun name _ => rows_mass state facts holds name)
    (fun name _ => members_mass state facts holds name)

/-- One causal store bound covers every tagged read, default, and reference. -/
theorem mass_stored (state : State Symbol Guard) (facts : Facts state)
    {bound : Nat} (stored : InternedValueMassHeap.Stored bound state) (input : Input) : mass state input ≤ bound := by
  cases input with
  | empty | ref => simpa only [mass, payload, InternedValueMass.value] using stored.positive
  | node name | mu name | union name =>
      simp only [mass, payload]
      cases found : SourcePreparedSharedRows.read state name with
      | none => simpa only [found, InternedValueMass.value] using stored.positive
      | some value =>
          dsimp only
          split
          · exact InternedValueMassHeap.available state stored value
              (SourcePreparedSharedRows.read_available state facts name value found)
          · simpa only [InternedValueMass.value] using stored.positive

/-- The local weight stays within the same causal payload bound. -/
theorem local_stored (state : State Symbol Guard) (facts : Facts state)
    {bound : Nat} (stored : InternedValueMassHeap.Stored bound state) (input : Input) :
    localSize (mass state) input ≤ bound :=
  Nat.le_trans (localSize_le (mass state) (fun name => mass_pos state (.ref name)) input)
    (mass_stored state facts stored input)

/-- The complete tagged input carrier has four tags per issued node identity. -/
theorem inventory_length (state : State Symbol Guard) : (inventory state).length = 1 + 4 * state.nodes.next := by
  simp only [inventory, List.length_cons, List.length_flatMap, List.length_nil,
    List.map_const', List.length_range, List.sum_replicate_nat]
  omega

/-- The literal ordered pair carrier has the square of the tagged carrier length. -/
theorem pairs_length (state : State Symbol Guard) :
    (inputPairs (inventory state)).length = (1 + 4 * state.nodes.next) * (1 + 4 * state.nodes.next) := by
  simp only [inputPairs, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate_nat, inventory_length]

end MicroCFTA.SourceRecursiveIntersectionMassInputBounds
