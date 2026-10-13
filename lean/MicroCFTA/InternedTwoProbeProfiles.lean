import MicroCFTA.InternedRootProfile

/-!
# Two distinct probes discriminate empty and direct-self bodies

A pure callback profile contains fixed captured references and optionally
its supplied argument. Source root filtering preserves empty status and
the direct-self case. Two distinct supplied names distinguish that case
from captured names, including captures equal to either probe name.
-/
namespace MicroCFTA.InternedTwoProbeProfiles
open InternedRootProfile
open InternedBinderProtocol (Reference)

/-- Normalization cannot remove the final reference from a pure profile. -/
theorem normalize_empty (name : Reference) (names : List Reference) :
    normalize name (some names) = some [] ↔ names = [] := by
  cases all : names.all (· == name) with
  | true => simp [normalize, all]
  | false =>
      obtain ⟨other, member, different⟩ := List.all_eq_false.mp all
      have retained : other ∈ names.filter (· != name) := List.mem_filter.mpr ⟨member, by simpa using different⟩
      have notEmpty : names.filter (· != name) ≠ [] := fun empty => by simp [empty] at retained
      have original : names ≠ [] := fun empty => by simp [empty] at member
      simp [normalize, all, notEmpty, original]

/-- A selected literal-self profile survives normalization exactly when it was already the entire profile. -/
theorem normalize_single (name : Reference) (names : List Reference) :
    Single name ((normalize name (some names)).getD []) ↔ Single name names := by
  cases all : names.all (· == name) with
  | true => simp [normalize, all]
  | false =>
      have notSingle : ¬ Single name names := by
        intro single
        have selected : names.all (· == name) = true :=
          List.all_eq_true.mpr (fun other member => by simp [single.2 other member])
        simp [all] at selected
      constructor
      · intro single
        have member := single.1
        simp [normalize, all] at member
      · intro single
        exact False.elim (notSingle single)

/-- Every other literal reference survives root self filtering. -/
theorem normalize_other (name other : Reference) (different : other ≠ name) (names : List Reference) :
    other ∈ (normalize name (some names)).getD [] ↔ other ∈ names := by
  cases all : names.all (· == name) <;> simp [normalize, all, different]

/-- A probe is empty exactly for an unused argument and no captured reference. -/
theorem probe_empty (captured : List Reference) (uses : Bool) (name : Reference) :
    probe captured uses name = some [] ↔ captured = [] ∧ uses = false := by
  rw [probe, normalize_empty]
  cases uses <;> simp [response]

/-- A fresh direct-self body has no captured reference and uses its supplied argument. -/
theorem response_single (captured : List Reference) (uses : Bool) (own : Reference) (fresh : own ∉ captured) :
    Single own (response captured uses own) ↔ captured = [] ∧ uses = true := by
  constructor
  · intro single
    have empty : captured = [] := by
      cases captured with
      | nil => rfl
      | cons first rest =>
          have same := single.2 first (by simp [response])
          exact False.elim (fresh (by simp [same]))
    refine ⟨empty, ?_⟩
    cases uses <;> simp_all [response, Single]
  · rintro ⟨rfl, rfl⟩
    simp [response, Single]

/-- Two distinct self-shaped probes exclude every fixed captured reference. -/
theorem two_single (captured : List Reference) (uses : Bool) (first second : Reference) (different : first ≠ second) :
    (Single first ((probe captured uses first).getD []) ∧ Single second ((probe captured uses second).getD [])) ↔
      captured = [] ∧ uses = true := by
  simp only [probe, normalize_single]
  constructor
  · rintro ⟨left, right⟩
    have empty : captured = [] := by
      cases captured with
      | nil => rfl
      | cons head tail =>
          have a := left.2 head (by simp [response])
          have b := right.2 head (by simp [response])
          exact False.elim (different (a.symm.trans b))
    refine ⟨empty, ?_⟩
    cases uses <;> simp_all [response, Single]
  · rintro ⟨rfl, rfl⟩
    simp [response, Single]

/-- The actual normalized fresh-own body is empty exactly when both source probe profiles are empty. -/
theorem body_empty_iff (captured : List Reference) (uses : Bool) (own first second : Reference) :
    probe captured uses own = some [] ↔
      probe captured uses first = some [] ∧ probe captured uses second = some [] := by
  simp only [probe_empty, and_self]

/-- The actual normalized fresh-own body is direct self exactly for the ordered distinct self-probe pair. -/
theorem body_self_iff (captured : List Reference) (uses : Bool) (own first second : Reference)
    (fresh : own ∉ captured) (different : first ≠ second) :
    Single own ((probe captured uses own).getD []) ↔
      Single first ((probe captured uses first).getD []) ∧ Single second ((probe captured uses second).getD []) := by
  rw [probe, normalize_single, response_single captured uses own fresh, two_single captured uses first second different]

/-- The actual source sentinel constructors are distinct at every cached probe depth. -/
theorem source_body_self_iff (captured : List Reference) (uses : Bool) (identity level : Nat)
    (fresh : Reference.interned identity ∉ captured) :
    Single (.interned identity) ((probe captured uses (.interned identity)).getD []) ↔
      Single .depth ((probe captured uses .depth).getD []) ∧
        Single (.uninterned level) ((probe captured uses (.uninterned level)).getD []) :=
  body_self_iff captured uses (.interned identity) .depth (.uninterned level) fresh (by simp)

end MicroCFTA.InternedTwoProbeProfiles
