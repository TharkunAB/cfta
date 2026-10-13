import MicroCFTA.InternedFreeNameRequest
import MicroCFTA.InternedBoundaryFreeAge

/-!
# Free-name bounds for the two actual recursive probes

The fresh body and the two probes have the same captured free names.
If the body has only old free names, both probes also have only old free
names. This excludes fresh literal boundaries. Fresh Mu boundaries need
a separate proof.
-/
namespace MicroCFTA.InternedFreeNameBoundary
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedBoundaryAtoms InternedBoundaryProvenance
open InternedObservedAbsence InternedBoundaryFreeAge
open InternedBinderProtocol (Reference NodeRef)

/-- An absent free name cannot occur as an exposed literal boundary. -/
theorem reference_absent (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (name : Reference)
    (absent : name ∉ value.free) : .ref name ∉ atoms value :=
  fun member => absent (ref_free name value state coherent available member)

/-- Old free names and old Mu boundaries exclude every fresh boundary. -/
theorem clear_of_old (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (cutoff : Nat)
    (freeOld : ∀ identity, .interned identity ∈ value.free → identity < cutoff)
    (muOld : ∀ identity, .mu identity ∈ atoms value → identity < cutoff) :
    Clear (Fresh cutoff) value := by
  intro atom member
  cases atom with
  | empty | node | union => simp [Fresh]
  | ref name =>
      cases name with
      | state | uninterned | depth | intersection => simp [Fresh]
      | interned identity =>
          have old := freeOld identity (ref_free _ value state coherent available member)
          simpa only [Fresh, Nat.not_le] using old
  | mu identity =>
      have old := muOld identity member
      simpa only [Fresh, Nat.not_le] using old

/-- The next reservation cannot occur in the captures decoded from an available depth probe. -/
theorem next_not_captured (depth : Value Symbol Guard) (captured : List Reference)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state depth)
    (same : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈ captured)) :
    .interned state.nodes.next ∉ captured := by
  intro member
  exact next_absent state.nodes coherent.valid.2 depth available.issued
    ((same (.interned state.nodes.next) (by intro impossible; cases impossible)).mpr member)

/-- Removing the fresh bound name retains the age bound of the actual body. -/
theorem captures_old (body : Value Symbol Guard) (bound cutoff : Nat) (captured : List Reference)
    (fresh : .interned bound ∉ captured)
    (same : ∀ name, name ≠ .interned bound → (name ∈ body.free ↔ name ∈ captured))
    (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff) :
    ∀ identity, .interned identity ∈ captured → identity < cutoff := by
  intro identity member
  by_cases equal : identity = bound
  · subst identity
    exact False.elim (fresh member)
  · exact old identity ((same (.interned identity) (fun names => equal (Reference.interned.inj names))).mpr member)

/-- Both actual sentinel probes retain the old free-name bound of the fresh body. -/
theorem probes_free_below (depth ordinary body : Value Symbol Guard) (bound cutoff : Nat)
    (captured : List Reference) (fresh : .interned bound ∉ captured)
    (depthSame : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈ captured))
    (ordinarySame : ∀ name, name ≠ .uninterned depth.depth → (name ∈ ordinary.free ↔ name ∈ captured))
    (bodySame : ∀ name, name ≠ .interned bound → (name ∈ body.free ↔ name ∈ captured))
    (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff) :
    (∀ identity, .interned identity ∈ depth.free → identity < cutoff) ∧
      (∀ identity, .interned identity ∈ ordinary.free → identity < cutoff) := by
  have capturedOld := captures_old body bound cutoff captured fresh bodySame old
  constructor
  · intro identity member
    exact capturedOld identity ((depthSame (.interned identity) (by intro impossible; cases impossible)).mp member)
  · intro identity member
    exact capturedOld identity ((ordinarySame (.interned identity) (by intro impossible; cases impossible)).mp member)

/-- Neither actual probe exposes a fresh literal boundary when the fresh body has only old free names. -/
theorem probes_reference_absent (depth ordinary body : Value Symbol Guard) (bound cutoff : Nat)
    (captured : List Reference) (fresh : .interned bound ∉ captured)
    (depthSame : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈ captured))
    (ordinarySame : ∀ name, name ≠ .uninterned depth.depth → (name ∈ ordinary.free ↔ name ∈ captured))
    (bodySame : ∀ name, name ≠ .interned bound → (name ∈ body.free ↔ name ∈ captured))
    (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff)
    (state : State Symbol Guard) (coherent : Coherent state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary) :
    ∀ identity, cutoff ≤ identity →
      .ref (.interned identity) ∉ atoms depth ∧ .ref (.interned identity) ∉ atoms ordinary := by
  have bounds := probes_free_below depth ordinary body bound cutoff captured fresh depthSame ordinarySame bodySame old
  intro identity later
  constructor
  · apply reference_absent depth state coherent depthAvailable
    intro member
    exact Nat.not_lt_of_ge later (bounds.1 identity member)
  · apply reference_absent ordinary state coherent ordinaryAvailable
    intro member
    exact Nat.not_lt_of_ge later (bounds.2 identity member)

/-- The remaining Mu-boundary bounds complete absence for both actual probes. -/
theorem probes_clear (depth ordinary body : Value Symbol Guard) (bound cutoff : Nat)
    (captured : List Reference) (fresh : .interned bound ∉ captured)
    (depthSame : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈ captured))
    (ordinarySame : ∀ name, name ≠ .uninterned depth.depth → (name ∈ ordinary.free ↔ name ∈ captured))
    (bodySame : ∀ name, name ≠ .interned bound → (name ∈ body.free ↔ name ∈ captured))
    (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff)
    (state : State Symbol Guard) (coherent : Coherent state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (depthMuOld : ∀ identity, .mu identity ∈ atoms depth → identity < cutoff)
    (ordinaryMuOld : ∀ identity, .mu identity ∈ atoms ordinary → identity < cutoff) :
    Clear (Fresh cutoff) depth ∧ Clear (Fresh cutoff) ordinary := by
  have bounds := probes_free_below depth ordinary body bound cutoff captured fresh depthSame ordinarySame bodySame old
  exact ⟨clear_of_old depth state coherent depthAvailable cutoff bounds.1 depthMuOld,
    clear_of_old ordinary state coherent ordinaryAvailable cutoff bounds.2 ordinaryMuOld⟩

end MicroCFTA.InternedFreeNameBoundary
