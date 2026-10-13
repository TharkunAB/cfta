import MicroCFTA.InternedBoundaryAtoms

/-!
# Boundary identities through root self-reference filtering

The source filter can remove only its supplied literal reference. Every
other boundary, including each Mu identity, survives exactly. The two
distinct source placeholders therefore cover the original boundary set.
-/
namespace MicroCFTA.InternedBoundaryFilter
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedLiveEdges InternedBoundaryAtoms
open InternedBinderProtocol (Reference NodeRef)

/-- Root self filtering preserves precisely every boundary other than the supplied reference. -/
theorem filter_atom_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (atom : NodeRef)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state value) (different : atom ≠ .ref name) :
    atom ∈ atoms (run (withoutSelfReference name value) state).1 ↔ atom ∈ atoms value := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact Iff.rfl
  case union entry members depth free =>
    split
    · rw [makeUnion_atom_iff (members.filter (fun member => member.referenceOf != .ref name)) state coherent cached linked live
        (fun value included => available.children value (List.mem_filter.mp included).1)]
      simp only [atoms, many_member]
      constructor
      · rintro ⟨value, member, present⟩
        exact ⟨value, (List.mem_filter.mp member).1, present⟩
      · rintro ⟨value, member, present⟩
        refine ⟨value, (withoutSelfReference_members name members value).mpr ⟨member, ?_⟩, present⟩
        intro same
        subst value
        simp [atoms, different] at present
    · exact Iff.rfl

/-- Two different root filters retain every original boundary in at least one result. -/
theorem two_filters [DecidableEq (EdgeKey Symbol Guard)] (first second : Reference) (different : first ≠ second)
    (value : Value Symbol Guard) (left right : State Symbol Guard)
    (lc : Coherent left) (rc : Coherent right) (lk : Cached left) (rk : Cached right)
    (ll : Linked left) (rl : Linked right) (lv : Live left) (rv : Live right)
    (la : Available left value) (ra : Available right value) (atom : NodeRef) (present : atom ∈ atoms value) :
    atom ∈ atoms (run (withoutSelfReference first value) left).1 ∨
      atom ∈ atoms (run (withoutSelfReference second value) right).1 := by
  by_cases selected : atom = .ref first
  · right
    exact (filter_atom_iff second atom value right rc rk rl rv ra
      (by intro equal; exact different (NodeRef.ref.inj (selected.symm.trans equal)))).mpr present
  · left
    exact (filter_atom_iff first atom value left lc lk ll lv la selected).mpr present

/-- Every Mu boundary survives either source placeholder filter without a freshness condition. -/
theorem filter_mu_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (identity : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state value) :
    .mu identity ∈ atoms (run (withoutSelfReference name value) state).1 ↔ .mu identity ∈ atoms value :=
  filter_atom_iff name (.mu identity) value state coherent cached linked live available (by simp)

end MicroCFTA.InternedBoundaryFilter
