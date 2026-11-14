import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.InternedBoundaryProvenance
import MicroCFTA.InternedBoundaryFreeAge
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

/-!
# Boundary atoms in the actual current source heap

The accepted source build has one complete universe owner when a Mu is stored.
Every closed available source value has only that owner's Mu boundary.
These statements concern the original completed build.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBoundaryAtoms InternedBoundaryProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey NodeRef Reference)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Every boundary atom has a literal reference or a Mu identity. -/
private theorem atom_shape {S G : Type} (value : Value S G) (atom : NodeRef)
    (member : atom ∈ atoms value) :
    (∃ name, atom = .ref name) ∨ ∃ identity, atom = .mu identity := by
  cases value with
  | empty => simp only [atoms, List.not_mem_nil] at member
  | reference name =>
      simp only [atoms] at member
      exact Or.inl ⟨name, List.mem_singleton.mp member⟩
  | mu entry body depth ordinary =>
      simp only [atoms] at member
      exact Or.inr ⟨entry.identity, List.mem_singleton.mp member⟩
  | node entry edges depth free =>
      simp only [atoms] at member
      obtain ⟨edge, included, child, selected, occurrence⟩ :=
        (edge_member edges atom).mp member
      exact atom_shape child atom occurrence
  | union entry members depth free =>
      simp only [atoms] at member
      obtain ⟨child, included, occurrence⟩ := (many_member members atom).mp member
      exact atom_shape child atom occurrence
termination_by sizeOf value
decreasing_by
  · have edgeSmall := List.sizeOf_lt_of_mem included
    cases edge with
    | mk edgeEntry children =>
        have childSmall := List.sizeOf_lt_of_mem selected
        simp only [EdgeValue.children] at childSmall
        simp_wf
        simp only [EdgeValue.mk.sizeOf_spec] at edgeSmall
        subst value
        simp only [Value.node.sizeOf_spec]
        omega
  · have childSmall := List.sizeOf_lt_of_mem included
    simp_wf
    subst value
    simp only [Value.union.sizeOf_spec]
    omega

/-- Closed values in the original source heap have only the same stored universe boundary. -/
theorem current_stored_universe_closed_startup_value_atoms
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (value : Value Symbol Guard) (available : Available sourceHeap value)
    (closed : value.free = []) :
    ∀ atom ∈ atoms value, atom = .mu entry.identity := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro item member; cases member)
  have facts : Facts sourceHeap := by simpa only [built, Outcome.state] using checked.facts
  rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
      lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
  · exact False.elim (noMu key entry body depth ordinary stored)
  · obtain ⟨owner, ownerBody, ownerDepth, ownerOrdinary, _ownerStored, _ownerAvailable,
        _ownerClosed, _ownerReplay, unique⟩ := someMu
    have selected := unique key entry body depth ordinary stored
    intro atom member
    rcases atom_shape value atom member with ⟨name, same⟩ | ⟨identity, same⟩
    · rw [same] at member
      have free := ref_free name value sourceHeap facts.coherent available member
      simp only [closed, List.not_mem_nil] at free
    · rw [same] at member
      obtain ⟨other, otherBody, otherDepth, otherOrdinary, identitySame, present⟩ :=
        mu_stored value sourceHeap available identity member
      have equal := (unique other.key other otherBody otherDepth otherOrdinary present).trans selected.symm
      have entries : other = entry := (Value.mu.inj equal).1
      rw [same, ← identitySame, entries]

/-- The original accepted root has only the same stored universe boundary. -/
theorem current_stored_universe_startup_root_atoms
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∀ atom ∈ atoms rootValue, atom = .mu entry.identity := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro item member; cases member)
  exact current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    rootValue (checked.result rootValue sourceHeap built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty (ordinarySymbols whole) rootValue sourceHeap built)

/-- The same build has no closed boundary atom or one original owner for every closed value. -/
theorem current_build_closed_startup_atoms
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap) :
    ((∀ (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard),
        sourceHeap.nodeRecords key ≠ some (.mu entry body depth ordinary)) ∧
      ∀ value : Value Symbol Guard, Available sourceHeap value → value.free = [] → atoms value = []) ∨
    ∃ (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard),
      sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Available sourceHeap (.mu entry body depth ordinary) ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      (∀ value : Value Symbol Guard, Available sourceHeap value → value.free = [] →
        ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro item member; cases member)
  have facts : Facts sourceHeap := by simpa only [built, Outcome.state] using checked.facts
  rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
      lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
  · refine Or.inl ⟨noMu, ?_⟩
    intro value available closed
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    rcases atom_shape value atom member with ⟨name, same⟩ | ⟨identity, same⟩
    · rw [same] at member
      have free := ref_free name value sourceHeap facts.coherent available member
      simp only [closed, List.not_mem_nil] at free
    · rw [same] at member
      obtain ⟨entry, body, depth, ordinary, _identitySame, present⟩ :=
        mu_stored value sourceHeap available identity member
      exact noMu entry.key entry body depth ordinary present
  · obtain ⟨entry, body, depth, ordinary, stored, available, closed, _replay, _unique⟩ := someMu
    exact Or.inr ⟨entry, body, depth, ordinary, stored, available, closed,
      current_stored_universe_closed_startup_value_atoms
        lib query signed whole accepted rootValue sourceHeap built (muKey depth ordinary)
        entry body depth ordinary stored⟩

/-- Original-U boundary atoms imply closedness in the same grown source heap. -/
theorem current_stored_universe_boundary_atoms_closed_after_growth
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (value : Value Symbol Guard) (available : Available heap value)
    (onlyU : ∀ atom ∈ atoms value, atom = .mu entry.identity) : value.free = [] := by
  rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
      lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
  · exact False.elim (noMu key entry body depth ordinary stored)
  · obtain ⟨_owner, _ownerBody, _ownerDepth, _ownerOrdinary, _ownerStored, _ownerAvailable,
        ownerClosed, _ownerReplay, unique⟩ := someMu
    have selected := unique key entry body depth ordinary stored
    have universeClosed : (Value.mu entry body depth ordinary).free = [] := by
      rw [selected]
      exact ownerClosed
    have universeAvailable : Available heap (.mu entry body depth ordinary) :=
      facts.cached.nodes key _ (growth.nodeRecords key _ stored)
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    rcases InternedBoundaryFreeAge.free_source value heap facts.coherent available name member with bare | boundary
    · have impossible := onlyU (.ref name) bare
      cases impossible
    · obtain ⟨other, otherBody, otherDepth, otherOrdinary, occurrence, resident, free⟩ := boundary
      have same : Value.mu other otherBody otherDepth otherOrdinary = .mu entry body depth ordinary :=
        InternedFreshProbeKeys.resident_reference_injective heap facts.coherent _ _
          resident.resident universeAvailable.resident
          (by simpa only [Value.referenceOf] using onlyU (.mu other.identity) occurrence)
      simp only [same, universeClosed, List.not_mem_nil] at free

end MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
