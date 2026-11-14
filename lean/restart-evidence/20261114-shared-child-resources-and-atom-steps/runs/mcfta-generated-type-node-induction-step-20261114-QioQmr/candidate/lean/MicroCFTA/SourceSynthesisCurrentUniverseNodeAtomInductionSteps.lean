-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps

/-!
# Ordered ordinary-node steps for boundary-atom induction

Actual edge readback retains its symbol, guard, and ordered children.
The node constructor selects atoms from those actual edge children.
Private helpers compose the native lower-fuel child calls in order.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseNodeAtomInductionSteps
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms InternedEdgeResidency
open SourceRecursiveIntersectionKernel

set_option autoImplicit false
variable {Symbol Guard : Type}

/-- Actual edge construction retains its literal fields and the supplied owner atoms. -/
theorem make_edge_atoms_checked [DecidableEq (EdgeKey Symbol Guard)]
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ownerId : Nat) (symbol : Symbol) (constraint : Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available state.heap value)
    (onlyU : ∀ value ∈ values, ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state (work (makeEdge symbol constraint values) state)
      (fun after edge => EdgeResident after.heap edge ∧ edge.entry.key.symbol = symbol ∧
        edge.entry.key.constraint = constraint ∧ edge.children = values ∧
        ∀ child ∈ edge.children, ∀ atom ∈ atoms child, atom = .mu ownerId) := by
  have native := work_checked state valid (makeEdge symbol constraint values) EdgeResident
    (InternedNestedFacts.edge_verified symbol constraint values state.heap valid.1 available)
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state.heap valid.1 symbol constraint values available
  refine ⟨native.valid, native.extension, ?_⟩
  intro edge after returned
  have same := (work_done (makeEdge symbol constraint values) state edge after returned).1
  have literal : edge.entry.key.symbol = symbol ∧ edge.entry.key.constraint = constraint ∧
      edge.children = values := by
    rw [same]
    exact fields
  refine ⟨native.result edge after returned, literal.1, literal.2.1, literal.2.2, ?_⟩
  intro child member atom occurrence
  have included : child ∈ values := by
    rw [← literal.2.2]
    exact member
  exact onlyU child included atom occurrence

/-- Actual node normalization selects atoms from the supplied resident edge children. -/
theorem make_node_atoms_checked [DecidableEq (EdgeKey Symbol Guard)]
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ownerId : Nat) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge)
    (onlyU : ∀ edge ∈ edges, ∀ child ∈ edge.children, ∀ atom ∈ atoms child, atom = .mu ownerId) :
    Checked state (work (makeNode edges) state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  have native := work_checked state valid (makeNode edges) Available
    (InternedNestedFacts.node_verified edges state.heap valid.1 resident)
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  have same := (work_done (makeNode edges) state value after returned).1
  refine ⟨native.result value after returned, ?_⟩
  intro atom occurrence
  rw [same] at occurrence
  have original := makeNode_atom_origin edges state.heap valid.1.coherent valid.1.linked resident atom occurrence
  obtain ⟨edge, present, child, member, included⟩ := (edge_member edges atom).mp original
  exact onlyU edge present child member atom included

/-- The actual edge step composes only native lower-fuel calls and retains mismatch behavior. -/
private theorem ordered_edge_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (ownerId : Nat)
    (fuelInduction : ∀ pair ∈ left.children.zip right.children, ∀ current : Machine Symbol Guard,
      SourceRecursiveIntersectionKernel.Valid current → Extension state current →
      ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin fuel domain pair.1 pair.2 current = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state (edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state)
      (fun after result => EdgeResident after.heap result ∧
        ∀ child ∈ result.children, ∀ atom ∈ atoms child, atom = .mu ownerId) := by
  unfold edge
  split
  · let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
      Extension state current ∧ Domain current domain ∧
        Available current.heap pair.1 ∧ Available current.heap pair.2
    let output := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
      Available current.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId
    have inputStable : Stable input := by
      intro before after extension pair previous
      exact ⟨previous.1.trans extension, previous.2.1.grows domain extension,
        extension.available pair.1 previous.2.2.1, extension.available pair.2 previous.2.2.2⟩
    have outputStable : Stable output := by
      intro before after extension value previous
      exact ⟨extension.available value previous.1, previous.2⟩
    have requests : Checked state
        (walk (fun pair current => execute emptyGuard conjoin fuel domain pair.1 pair.2 current)
          (left.children.zip right.children) state)
        (fun after values => ∀ value ∈ values, output after value) := by
      apply walk_checked _ (left.children.zip right.children) input output inputStable outputStable
      · intro pair present current currentValid currentInput
        have native := execute_checked emptyGuard conjoin fuel domain pair.1 pair.2 current
          currentValid currentInput.2.1 currentInput.2.2.1 currentInput.2.2.2
        refine ⟨native.valid, native.extension, ?_⟩
        intro value after returned
        exact ⟨native.result value after returned,
          fuelInduction pair present current currentValid currentInput.1 value after returned⟩
      · exact valid
      · intro pair present
        have included := List.of_mem_zip present
        exact ⟨Extension.refl state, known,
          valid.1.cached.edges left.entry.key left leftResident pair.1 included.1,
          valid.1.cached.edges right.entry.key right rightResident pair.2 included.2⟩
    apply checked_bind state _ _ _ _ requests
    intro values after _ afterValid properties
    have built := make_edge_atoms_checked after afterValid ownerId left.entry.key.symbol
      (conjoin left.entry.key.constraint right.entry.key.constraint) values
      (fun value present => (properties value present).1)
      (fun value present => (properties value present).2)
    refine ⟨built.valid, built.extension, ?_⟩
    intro result final returned
    have fields := built.result result final returned
    exact ⟨fields.1, fields.2.2.2.2⟩
  · have emptyAvailable : ∀ value ∈ [Value.empty (Symbol := Symbol) (Guard := Guard)],
        Available state.heap value := by
      intro value member
      rw [List.mem_singleton.mp member]
      exact empty_available state.heap
    have emptyAtoms : ∀ value ∈ [Value.empty (Symbol := Symbol) (Guard := Guard)],
        ∀ atom ∈ atoms value, atom = .mu ownerId := by
      intro value member atom occurrence
      rw [List.mem_singleton.mp member] at occurrence
      simp only [atoms, List.not_mem_nil] at occurrence
    have built := make_edge_atoms_checked state valid ownerId left.entry.key.symbol emptyGuard [.empty]
      emptyAvailable emptyAtoms
    refine ⟨built.valid, built.extension, ?_⟩
    intro result final returned
    have fields := built.result result final returned
    exact ⟨fields.1, fields.2.2.2.2⟩

/-- The actual ordered hash join and node constructor preserve the lower-fuel owner atoms. -/
private theorem ordered_node_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.heap row) (ownerId : Nat)
    (fuelInduction : ∀ pair ∈ pairs left right, ∀ children ∈ pair.1.children.zip pair.2.children,
      ∀ current : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid current →
      Extension state current → ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin fuel domain children.1 children.2 current = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state (node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Extension state current ∧ Domain current domain ∧
      EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2
  let output := fun (current : Machine Symbol Guard) (row : EdgeValue Symbol Guard) =>
    EdgeResident current.heap row ∧ ∀ child ∈ row.children, ∀ atom ∈ atoms child, atom = .mu ownerId
  have inputStable : Stable input := by
    intro before after extension pair previous
    exact ⟨previous.1.trans extension, previous.2.1.grows domain extension,
      edge_grows before.heap after.heap extension.heap pair.1 previous.2.2.1,
      edge_grows before.heap after.heap extension.heap pair.2 previous.2.2.2⟩
  have outputStable : Stable output := by
    intro before after extension row previous
    exact ⟨edge_grows before.heap after.heap extension.heap row previous.1, previous.2⟩
  have requests : Checked state
      (walk (fun pair => edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) pair.1 pair.2)
        (pairs left right) state)
      (fun after values => ∀ row ∈ values, output after row) := by
    apply walk_checked _ (pairs left right) input output inputStable outputStable
    · intro pair present current currentValid currentInput
      apply ordered_edge_atoms_of_fuel_induction emptyGuard conjoin fuel domain pair.1 pair.2 current
        currentValid currentInput.2.1 currentInput.2.2.1 currentInput.2.2.2 ownerId
      intro children member later laterValid growth value after returned
      exact fuelInduction pair present children member later laterValid
        (currentInput.1.trans growth) value after returned
    · exact valid
    · intro pair present
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp present
      exact ⟨Extension.refl state, known, leftResident pair.1 first, rightResident pair.2 second⟩
  unfold node
  apply checked_bind state _ _ _ _ requests
  intro values after _ afterValid properties
  exact make_node_atoms_checked after afterValid ownerId values
    (fun row member => (properties row member).1)
    (fun row member => (properties row member).2)

/-- The selected ordinary branch derives its closed child inputs from the actual parent records. -/
private theorem ordinary_closed_nodes_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (leftEntry rightEntry : Interned NodeKey) (leftRows rightRows : List (EdgeValue Symbol Guard))
    (leftDepth rightDepth : Nat) (leftFree rightFree : List Reference)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (ownerId : Nat)
    (leftAvailable : Available state.heap (.node leftEntry leftRows leftDepth leftFree))
    (rightAvailable : Available state.heap (.node rightEntry rightRows rightDepth rightFree))
    (leftClosed : (Value.node leftEntry leftRows leftDepth leftFree).free = [])
    (rightClosed : (Value.node rightEntry rightRows rightDepth rightFree).free = [])
    (leftAtoms : ∀ atom ∈ atoms (.node leftEntry leftRows leftDepth leftFree), atom = .mu ownerId)
    (rightAtoms : ∀ atom ∈ atoms (.node rightEntry rightRows rightDepth rightFree), atom = .mu ownerId)
    (selected : SourceRecursiveIntersectionControl.decision domain.key
      (.node leftEntry leftRows leftDepth leftFree) (.node rightEntry rightRows rightDepth rightFree) = .ordinary)
    (fuelInduction : ∀ (left right : Value Symbol Guard) (current : Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid current → Extension state current →
      Available current.heap left → Available current.heap right → left.free = [] → right.free = [] →
      (∀ atom ∈ atoms left, atom = .mu ownerId) → (∀ atom ∈ atoms right, atom = .mu ownerId) →
      ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin fuel domain left right current = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state
      (execute emptyGuard conjoin (fuel + 1) domain
        (.node leftEntry leftRows leftDepth leftFree) (.node rightEntry rightRows rightDepth rightFree) state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  simp only [execute, onNode, selected]
  apply ordered_node_atoms_of_fuel_induction emptyGuard conjoin fuel domain leftRows rightRows state valid known
    (fun row present => valid.1.linked leftEntry.key _ (leftAvailable.resident leftEntry rfl) row present)
    (fun row present => valid.1.linked rightEntry.key _ (rightAvailable.resident rightEntry rfl) row present) ownerId
  intro pair present children member current currentValid growth value after returned
  have matched := (pairs_member leftRows rightRows pair).mp present
  have included := List.of_mem_zip member
  have first := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms state.heap valid.1 ownerId
    leftEntry leftRows leftDepth leftFree leftAvailable leftClosed leftAtoms pair.1 matched.1 children.1 included.1
  have second := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms state.heap valid.1 ownerId
    rightEntry rightRows rightDepth rightFree rightAvailable rightClosed rightAtoms pair.2 matched.2.1 children.2 included.2
  exact fuelInduction children.1 children.2 current currentValid growth
    (growth.available children.1 first.1) (growth.available children.2 second.1)
    first.2.1 second.2.1 first.2.2 second.2.2 value after returned

end MicroCFTA.SourceSynthesisCurrentUniverseNodeAtomInductionSteps
