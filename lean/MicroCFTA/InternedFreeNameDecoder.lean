import MicroCFTA.InternedNormalizationFree
import MicroCFTA.InternedProfileCallbackForm
import MicroCFTA.InternedNestedMissReadback

/-!
# Two source probes decode captured free names

Each probe can add its supplied argument as a free name. Remove that
name from its own result, then combine the two results. Distinct probe
names recover every captured name, including either probe sentinel.
-/
namespace MicroCFTA.InternedFreeNameDecoder
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedRootProfile InternedProfileCallbackForm InternedNormalizationFree
open InternedBinderProtocol (Reference NodeKey)

/-- Remove each supplied probe name only from its own free-name result. -/
def decode (firstName secondName : Reference) (first second : List Reference) : List Reference :=
  first.filter (· != firstName) ++ second.filter (· != secondName)

/-- Distinct probes recover exactly the captured free-name set. -/
theorem decode_responses (captured : List Reference) (uses : Bool)
    (firstName secondName : Reference) (different : firstName ≠ secondName) (name : Reference) :
    name ∈ decode firstName secondName (response captured uses firstName) (response captured uses secondName) ↔
      name ∈ captured := by
  simp only [decode, List.mem_append, List.mem_filter, bne_iff_ne, response_member]
  constructor
  · rintro (⟨included, other⟩ | ⟨included, other⟩)
    · rcases included with captured | ⟨_, same⟩
      · exact captured
      · exact False.elim (other same)
    · rcases included with captured | ⟨_, same⟩
      · exact captured
      · exact False.elim (other same)
  · intro included
    by_cases first : name = firstName
    · exact Or.inr ⟨Or.inl included, by simpa only [first] using different⟩
    · exact Or.inl ⟨Or.inl included, first⟩

/-- The decoder needs only each probe's behavior away from its own supplied name. -/
theorem decode_observed (captured first second : List Reference)
    (firstName secondName : Reference) (different : firstName ≠ secondName)
    (firstSame : ∀ name, name ≠ firstName → (name ∈ first ↔ name ∈ captured))
    (secondSame : ∀ name, name ≠ secondName → (name ∈ second ↔ name ∈ captured))
    (name : Reference) : name ∈ decode firstName secondName first second ↔ name ∈ captured := by
  simp only [decode, List.mem_append, List.mem_filter, bne_iff_ne]
  constructor
  · rintro (⟨included, other⟩ | ⟨included, other⟩)
    · exact (firstSame name other).mp included
    · exact (secondSame name other).mp included
  · intro included
    by_cases firstDifferent : name = firstName
    · have other : name ≠ secondName := by simpa only [firstDifferent] using different
      exact Or.inr ⟨(secondSame name other).mpr included, other⟩
    · exact Or.inl ⟨(firstSame name firstDifferent).mpr included, firstDifferent⟩

/-- Raw and smart construction store the same free-name field. -/
theorem finish_free (smart : Bool) (value : Value Symbol Guard) : (finish smart value).free = value.free := by
  cases smart <;> simp [finish, cleanup_free]

/-- A completed Mu removes only its fresh bound name from the actual body free names. -/
theorem candidate_free (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (name : Reference) :
    name ∈ (finish smart (.mu entry body depth ordinary)).free ↔
      name ∈ body.free ∧ name ≠ .interned entry.identity := by
  rw [finish_free]
  simp [Value.free]

/-- Source body membership and two distinct actual probe observations determine the complete candidate free-name set. -/
theorem candidate_decoded (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (captured : List Reference) (firstName secondName : Reference) (different : firstName ≠ secondName)
    (fresh : .interned entry.identity ∉ captured)
    (bodySame : ∀ name, name ≠ .interned entry.identity → (name ∈ body.free ↔ name ∈ captured))
    (firstSame : ∀ name, name ≠ firstName → (name ∈ depth.free ↔ name ∈ captured))
    (secondSame : ∀ name, name ≠ secondName → (name ∈ ordinary.free ↔ name ∈ captured))
    (name : Reference) :
    name ∈ (finish smart (.mu entry body depth ordinary)).free ↔
      name ∈ decode firstName secondName depth.free ordinary.free := by
  rw [candidate_free, decode_observed captured depth.free ordinary.free firstName secondName different firstSame secondSame name]
  constructor
  · rintro ⟨included, other⟩
    exact (bodySame name other).mp included
  · intro included
    have other : name ≠ .interned entry.identity := by
      intro same
      exact fresh (same ▸ included)
    exact ⟨(bodySame name other).mpr included, other⟩

end MicroCFTA.InternedFreeNameDecoder
