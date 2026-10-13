import MicroCFTA.InternedProfileOrigins

/-!
# Recover a smart result profile from its two probes

The two supplied probe names are distinct. A pair of direct-self profiles
therefore means that the smart result is empty. In every other pure case,
the union of both probe reference sets is exactly the fixed capture set.
This also covers captures that equal either supplied probe name.
-/
namespace MicroCFTA.InternedProbeDecoder
open InternedRootProfile InternedTwoProbeProfiles InternedProfileCallbackForm
open InternedBinderProtocol (Reference)

/-- Decide whether a pure profile contains exactly the selected reference. -/
def single (name : Reference) (names : List Reference) : Bool :=
  names.contains name && names.all (· == name)

/-- Decode the smart result profile from the ordered normalized probe pair. -/
def decode (firstName secondName : Reference) : Profile → Profile → Profile
  | some first, some second =>
      some (if single firstName first && single secondName second then [] else first ++ second)
  | _, _ => none

/-- The executable direct-self decision has the stated set interpretation. -/
theorem single_iff (name : Reference) (names : List Reference) :
    single name names = true ↔ Single name names := by
  simp [single, Single, List.all_eq_true]

/-- A normalized pure probe stays pure. -/
theorem probe_pure (captured : List Reference) (uses : Bool) (name : Reference) :
    ∃ names, probe captured uses name = some names := by
  unfold probe normalize
  exact ⟨_, rfl⟩

/-- A probe reference outside the captures requires the empty-capture direct-self case. -/
theorem probe_extra (captured : List Reference) (uses : Bool) (argument name : Reference)
    (member : name ∈ (probe captured uses argument).getD []) (absent : name ∉ captured) :
    captured = [] ∧ uses = true ∧ name = argument := by
  cases all : (response captured uses argument).all (· == argument) with
  | false =>
      have retained : name ∈ (response captured uses argument).filter (· != argument) := by
        simpa [probe, normalize, all] using member
      obtain ⟨original, different⟩ := List.mem_filter.mp retained
      rcases (response_member captured uses argument name).mp original with fixed | ⟨_, same⟩
      · exact False.elim (absent fixed)
      · simp [same] at different
  | true =>
      have original : name ∈ response captured uses argument := by simpa [probe, normalize, all] using member
      rcases (response_member captured uses argument name).mp original with fixed | ⟨used, same⟩
      · exact False.elim (absent fixed)
      · refine ⟨?_, used, same⟩
        cases captured with
        | nil => rfl
        | cons head rest =>
            have headSame : head = argument := by
              simpa using List.all_eq_true.mp all head (by simp [response])
            exact False.elim (absent (by simp [same, headSame]))

/-- With a nonempty capture set, each probe reference comes from that set. -/
theorem probe_subset (captured : List Reference) (uses : Bool) (argument name : Reference)
    (nonempty : captured ≠ []) (member : name ∈ (probe captured uses argument).getD []) : name ∈ captured := by
  by_cases present : name ∈ captured
  · exact present
  · exact False.elim (nonempty (probe_extra captured uses argument name member present).1)

/-- Distinct self filters cannot both remove one fixed captured name. -/
theorem probes_cover (captured : List Reference) (uses : Bool) (first second name : Reference)
    (different : first ≠ second) (member : name ∈ captured) :
    name ∈ (probe captured uses first).getD [] ∨ name ∈ (probe captured uses second).getD [] := by
  by_cases selected : name = first
  · right
    have other : name ≠ second := selected ▸ different
    apply (normalize_other second name other (response captured uses second)).mpr
    simp [response, member]
  · left
    apply (normalize_other first name selected (response captured uses first)).mpr
    simp [response, member]

/-- Two normalized probes recover the exact smart-result capture set. -/
theorem decode_probes (captured : List Reference) (uses : Bool) (first second : Reference)
    (different : first ≠ second) :
    Equivalent (decode first second (probe captured uses first) (probe captured uses second)) (some captured) := by
  by_cases empty : captured = []
  · subst captured
    cases uses <;> simp [Equivalent, decode, probe, normalize, response, single]
  · obtain ⟨left, leftProbe⟩ := probe_pure captured uses first
    obtain ⟨right, rightProbe⟩ := probe_pure captured uses second
    have notBoth : (single first left && single second right) = false := by
      cases selected : single first left && single second right with
      | false => rfl
      | true =>
          have both : Single first left ∧ Single second right := by
            simpa only [Bool.and_eq_true, single_iff] using selected
          have pair : Single first ((probe captured uses first).getD []) ∧
              Single second ((probe captured uses second).getD []) := by simpa [leftProbe, rightProbe] using both
          exact False.elim (empty ((two_single captured uses first second different).mp pair).1)
    rw [leftProbe, rightProbe]
    constructor
    · simp [decode, notBoth]
    · intro name
      simp only [decode, notBoth, Bool.false_eq_true, ↓reduceIte, Option.getD_some, List.mem_append]
      constructor
      · intro member
        rcases member with leftMember | rightMember
        · exact probe_subset captured uses first name empty (by simpa [leftProbe] using leftMember)
        · exact probe_subset captured uses second name empty (by simpa [rightProbe] using rightMember)
      · intro member
        simpa [leftProbe, rightProbe] using probes_cover captured uses first second name different member

end MicroCFTA.InternedProbeDecoder
