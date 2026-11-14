import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.InternedBoundaryAtoms
import MicroCFTA.InternedNormalizationFree

/-!
# Physical inputs and an ordered union step for atom induction

Closed parent records supply closed available children with the same atoms.
Actual union construction preserves those atoms through normalization.
The private ordered-walk step has an explicit lower-fuel induction hypothesis.
It is not the closed generated-type theorem.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms InternedNormalizationFree
open SourceRecursiveIntersectionKernel

set_option autoImplicit false
variable {Symbol Guard : Type}

/-- An actual union member inherits closedness and the original owner's boundary atoms. -/
theorem union_member_closed_atoms (heap : State Symbol Guard) (facts : Facts heap) (ownerId : Nat)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available heap (.union entry members depth free))
    (closed : (Value.union entry members depth free).free = [])
    (onlyU : ∀ atom ∈ atoms (.union entry members depth free), atom = .mu ownerId)
    (child : Value Symbol Guard) (member : child ∈ members) :
    Available heap child ∧ child.free = [] ∧ ∀ atom ∈ atoms child, atom = .mu ownerId := by
  have metadata := union_free heap facts.coherent entry members depth free available.resident
  have freeEmpty : free = [] := by simpa only [Value.free] using closed
  refine ⟨available.children child member, ?_, ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro name named
    have parentName : name ∈ free := by
      rw [metadata, childFree_member]
      exact ⟨child, member, named⟩
    simp only [freeEmpty, List.not_mem_nil] at parentName
  · intro atom occurrence
    apply onlyU atom
    simpa only [atoms] using (many_member members atom).mpr ⟨child, member, occurrence⟩

/-- An actual ordered node child inherits closedness and the original owner's boundary atoms. -/
theorem node_child_closed_atoms (heap : State Symbol Guard) (facts : Facts heap) (ownerId : Nat)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available heap (.node entry edges depth free))
    (closed : (Value.node entry edges depth free).free = [])
    (onlyU : ∀ atom ∈ atoms (.node entry edges depth free), atom = .mu ownerId)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) :
    Available heap child ∧ child.free = [] ∧ ∀ atom ∈ atoms child, atom = .mu ownerId := by
  have included : child ∈ edges.flatMap EdgeValue.children := List.mem_flatMap.mpr ⟨edge, present, member⟩
  have metadata := node_free heap facts.coherent entry edges depth free available.resident
  have freeEmpty : free = [] := by simpa only [Value.free] using closed
  refine ⟨available.children child included, ?_, ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro name named
    have parentName : name ∈ free := by
      rw [metadata, childFree_member]
      exact ⟨child, included, named⟩
    simp only [freeEmpty, List.not_mem_nil] at parentName
  · intro atom occurrence
    apply onlyU atom
    simpa only [atoms] using (edge_member edges atom).mpr ⟨edge, present, child, member, occurrence⟩

/-- Actual union normalization returns an available value with only the supplied original owner atom. -/
theorem make_union_atoms_checked [DecidableEq (EdgeKey Symbol Guard)]
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ownerId : Nat) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available state.heap value)
    (onlyU : ∀ value ∈ values, ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state (work (makeUnion values) state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  have native := work_checked state valid (makeUnion values) Available
    (InternedNestedFacts.union_verified values state.heap valid.1 available)
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  have same := (work_done (makeUnion values) state value after returned).1
  refine ⟨native.result value after returned, ?_⟩
  intro atom occurrence
  rw [same] at occurrence
  obtain ⟨original, member, present⟩ := makeUnion_atom_origin values state.heap
    valid.1.coherent valid.1.cached valid.1.linked available atom occurrence
  exact onlyU original member atom present

/-- Auxiliary union payload step under the explicit lower-fuel induction hypothesis. -/
private theorem ordered_union_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (otherAvailable : Available state.heap other)
    (membersAvailable : ∀ member ∈ members, Available state.heap member) (ownerId : Nat)
    (fuelInduction : ∀ member ∈ members, ∀ current : Machine Symbol Guard,
      SourceRecursiveIntersectionKernel.Valid current → Extension state current →
      ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      (if left then execute emptyGuard conjoin fuel domain member other current
        else execute emptyGuard conjoin fuel domain other member current) = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state
      ((walk (fun member current => if left then execute emptyGuard conjoin fuel domain member other current
        else execute emptyGuard conjoin fuel domain other member current) members state).bind
          (fun values after => work (makeUnion values) after))
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  let input := fun (current : Machine Symbol Guard) (member : Value Symbol Guard) =>
    Extension state current ∧ Domain current domain ∧
      Available current.heap other ∧ Available current.heap member
  let output := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available current.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId
  have inputStable : Stable input := by
    intro before after extension member previous
    exact ⟨previous.1.trans extension, previous.2.1.grows domain extension,
      extension.available other previous.2.2.1, extension.available member previous.2.2.2⟩
  have outputStable : Stable output := by
    intro before after extension value previous
    exact ⟨extension.available value previous.1, previous.2⟩
  have requests : Checked state
      (walk (fun member current => if left then execute emptyGuard conjoin fuel domain member other current
        else execute emptyGuard conjoin fuel domain other member current) members state)
      (fun after values => ∀ value ∈ values, output after value) := by
    apply walk_checked _ members input output inputStable outputStable
    · intro member present current currentValid currentInput
      cases left with
      | false =>
          have native := execute_checked emptyGuard conjoin fuel domain other member current
            currentValid currentInput.2.1 currentInput.2.2.1 currentInput.2.2.2
          refine ⟨native.valid, native.extension, ?_⟩
          intro value after returned
          exact ⟨native.result value after returned,
            fuelInduction member present current currentValid currentInput.1 value after returned⟩
      | true =>
          have native := execute_checked emptyGuard conjoin fuel domain member other current
            currentValid currentInput.2.1 currentInput.2.2.2 currentInput.2.2.1
          refine ⟨native.valid, native.extension, ?_⟩
          intro value after returned
          exact ⟨native.result value after returned,
            fuelInduction member present current currentValid currentInput.1 value after returned⟩
    · exact valid
    · intro member present
      exact ⟨Extension.refl state, known, otherAvailable, membersAvailable member present⟩
  apply checked_bind state _ _ _ _ requests
  intro values after returned afterValid properties
  exact make_union_atoms_checked after afterValid ownerId values
    (fun value present => (properties value present).1)
    (fun value present => (properties value present).2)

end MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
