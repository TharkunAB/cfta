import MicroCFTA.RecursiveSource

/-!
# Finite witnesses for computed minimum sizes

Minimum metadata must identify an actual member as well as bound all members.
The finite source proof supplies witnesses at each computed minimum. The
recursive probe carries those witnesses through every decreasing assumption.
-/

namespace MicroCFTA.MinimumWitness
open FiniteSource RecursiveSource

/-- Every successful finite-source minimum is attained by an actual size-class member. -/
theorem finite_attains (description : Source α) (size : Nat)
    (found : SourceMinimum.minimum description = some size) : ∃ value, value ∈ classMembers description size := by
  induction description generalizing size with
  | source outcomes positive =>
      have nonempty : outcomes ≠ [] := by intro empty; simp [SourceMinimum.minimum, empty] at found
      have same : size = 1 := by simpa [SourceMinimum.minimum, List.isEmpty_eq_false_iff.mpr nonempty] using found.symm
      obtain ⟨entry, present⟩ := List.exists_mem_of_ne_nil outcomes nonempty
      exact ⟨entry.2, by simp [classMembers, same]; exact ⟨entry.1, present⟩⟩
  | pure value =>
      have same : size = 0 := Option.some.inj found.symm
      exact ⟨value, by simp [classMembers, same]⟩
  | map transform inner ih =>
      obtain ⟨value, present⟩ := ih size found
      exact ⟨transform value, List.mem_map.mpr ⟨value, present, rfl⟩⟩
  | pay inner ih =>
      cases before : SourceMinimum.minimum inner with
      | none => simp [SourceMinimum.minimum, before] at found
      | some lower =>
          have same : size = lower + 1 := by simpa [SourceMinimum.minimum, before] using found.symm
          obtain ⟨value, present⟩ := ih lower before
          exact ⟨value, by simpa [classMembers, same] using present⟩
  | atomic inner ih =>
      have nonempty : members inner ≠ [] := by intro empty; simp [SourceMinimum.minimum, empty] at found
      have same : size = 1 := by simpa [SourceMinimum.minimum, List.isEmpty_eq_false_iff.mpr nonempty] using found.symm
      obtain ⟨value, present⟩ := List.exists_mem_of_ne_nil (members inner) nonempty
      exact ⟨value, by simpa [classMembers, same] using present⟩
  | shared key inner ih => exact ih size found
  | choice lw rw lp rp left right ihl ihr =>
      rcases MinimumSize.best_source (SourceMinimum.minimum left) (SourceMinimum.minimum right) size found with fromLeft | fromRight
      · obtain ⟨value, present⟩ := ihl size fromLeft
        exact ⟨value, List.mem_append_left _ present⟩
      · obtain ⟨value, present⟩ := ihr size fromRight
        exact ⟨value, List.mem_append_right _ present⟩
  | ap functions arguments ihf iha =>
      cases left : SourceMinimum.minimum functions with
      | none => simp [SourceMinimum.minimum, RecursionProbe.productMinimum, left] at found
      | some leftSize =>
          cases right : SourceMinimum.minimum arguments with
          | none => simp [SourceMinimum.minimum, RecursionProbe.productMinimum, left, right] at found
          | some rightSize =>
              have same : size = leftSize + rightSize := by
                simpa [SourceMinimum.minimum, RecursionProbe.productMinimum, left, right] using found.symm
              obtain ⟨function, functionMember⟩ := ihf leftSize left
              obtain ⟨argument, argumentMember⟩ := iha rightSize right
              refine ⟨function argument, ?_⟩
              simp only [classMembers, Decoder.applyValues, List.mem_flatMap, List.mem_map]
              exact ⟨leftSize, List.mem_range.mpr (by omega), function, functionMember, argument,
                by simpa [same] using argumentMember, rfl⟩
  | sized classes positive bound =>
      have live := (List.min?_eq_some_iff.mp found).1
      have parts := List.mem_filter.mp live
      have within : size ≤ bound := by have := List.mem_range.mp parts.1; omega
      have nonempty : classes size ≠ [] := by intro empty; simp [empty] at parts
      obtain ⟨entry, present⟩ := List.exists_mem_of_ne_nil (classes size) nonempty
      exact ⟨entry.2, by simp [classMembers, within]; exact ⟨entry.1, present⟩⟩

/-- A body minimum has a finite derivation whenever the assumed occurrence minimum already has one. -/
theorem recipe_attains (body : Recipe Root Root) (recipe : Recipe Root α) (assumed : Option Nat)
    (witness : ∀ size, assumed = some size → ∃ value, Derives body body value size)
    (size : Nat) (found : RecursiveSource.minimum recipe assumed = some size) :
    ∃ value, Derives body recipe value size := by
  induction recipe generalizing size with
  | finite source =>
      obtain ⟨value, present⟩ := finite_attains source size found
      exact ⟨value, .finite source value size present⟩
  | occurrence =>
      obtain ⟨value, derived⟩ := witness size found
      exact ⟨value, .occurrence value size derived⟩
  | map transform inner ih =>
      obtain ⟨value, derived⟩ := ih size found
      exact ⟨transform value, .map transform inner value size derived⟩
  | pay inner ih =>
      change (RecursiveSource.minimum inner assumed).map (· + 1) = some size at found
      cases before : RecursiveSource.minimum inner assumed with
      | none => simp [before] at found
      | some lower =>
          have same : size = lower + 1 := by simpa [before] using found.symm
          obtain ⟨value, derived⟩ := ih lower before
          exact ⟨value, same ▸ Derives.pay inner value lower derived⟩
  | choice left right ihl ihr =>
      rcases MinimumSize.best_source (RecursiveSource.minimum left assumed)
        (RecursiveSource.minimum right assumed) size found with fromLeft | fromRight
      · obtain ⟨value, derived⟩ := ihl size fromLeft
        exact ⟨value, .left left right value size derived⟩
      · obtain ⟨value, derived⟩ := ihr size fromRight
        exact ⟨value, .right left right value size derived⟩
  | ap functions arguments ihf iha =>
      change RecursionProbe.productMinimum (RecursiveSource.minimum functions assumed)
        (RecursiveSource.minimum arguments assumed) = some size at found
      cases left : RecursiveSource.minimum functions assumed with
      | none => simp [RecursionProbe.productMinimum, left] at found
      | some leftSize =>
          cases right : RecursiveSource.minimum arguments assumed with
          | none => simp [RecursionProbe.productMinimum, left, right] at found
          | some rightSize =>
              have same : size = leftSize + rightSize := by simpa [RecursionProbe.productMinimum, left, right] using found.symm
              obtain ⟨function, functionDerived⟩ := ihf leftSize left
              obtain ⟨argument, argumentDerived⟩ := iha rightSize right
              exact ⟨function argument, same ▸ Derives.ap functions arguments function argument _ _ functionDerived argumentDerived⟩

/-- Each decreasing finite probe step preserves an actual witness for the retained minimum. -/
theorem finiteProbe_witness (body : Recipe Root Root) (assumed : Nat)
    (witness : ∃ value, Derives body body value assumed) :
    ∀ size, (RecursionProbe.convergeFinite
      (RecursionProbe.expressionBody (minimumExpr body) true false false) assumed).assumption = some size →
      ∃ value, Derives body body value size := by
  induction assumed using Nat.strongRecOn with
  | ind assumed ih =>
      rw [RecursionProbe.convergeFinite]
      cases found : RecursionProbe.minimum
        (RecursionProbe.expressionBody (minimumExpr body) true false false (some assumed)) with
      | none =>
          intro size same
          have equal : assumed = size := Option.some.inj same
          exact equal ▸ witness
      | some reached =>
          by_cases smaller : reached < assumed
          · simp only [dite_eq_left smaller]
            apply ih reached smaller
            apply recipe_attains body body (some assumed) _ reached found
            intro size same
            have equal : assumed = size := Option.some.inj same
            exact equal ▸ witness
          · simp only [dite_eq_right smaller]
            intro size same
            have equal : assumed = size := Option.some.inj same
            exact equal ▸ witness

/-- The source probe invents no finite minimum: each returned size has a finite recursive derivation. -/
theorem assumption_attains (body : Recipe Root Root) (size : Nat) (found : assumption body = some size) :
    ∃ value, Derives body body value size := by
  unfold assumption at found
  rw [RecursionProbe.converge] at found
  change (match RecursiveSource.minimum body none with
    | none => RecursionProbe.Result.mk none _ 1
    | some reached =>
        let result := RecursionProbe.convergeFinite
          (RecursionProbe.expressionBody (minimumExpr body) true false false) reached
        {result with steps := result.steps + 1}).assumption = some size at found
  cases first : RecursiveSource.minimum body none with
  | none => simp [first] at found
  | some reached =>
      have witness : ∃ value, Derives body body value reached :=
        recipe_attains body body none (by intros; contradiction) reached first
      exact finiteProbe_witness body reached witness size (by simpa only [first] using found)

/-- An empty result from minimum probing is equivalent to absence of every finite recursive derivation. -/
theorem assumption_none_exact (body : Recipe Root Root) :
    assumption body = none ↔ ¬ ∃ value size, Derives body body value size := by
  constructor
  · intro absent ⟨value, size, derived⟩
    obtain ⟨lower, found, _⟩ := derives_minimum body (assumption body) (assumption_fixed body) body value size derived
    rw [assumption_fixed, absent] at found
    contradiction
  · intro empty
    cases found : assumption body with
    | none => rfl
    | some size =>
        obtain ⟨value, derived⟩ := assumption_attains body size found
        exact False.elim (empty ⟨value, size, derived⟩)

/-- A successful probe returns exactly the least attained member size. -/
theorem assumption_minimum (body : Recipe Root Root) (size : Nat) (found : assumption body = some size) :
    (∃ value, Derives body body value size) ∧ ∀ value other, Derives body body value other → size ≤ other := by
  refine ⟨assumption_attains body size found, ?_⟩
  intro value other derived
  obtain ⟨lower, present, bound⟩ := derives_minimum body (assumption body) (assumption_fixed body) body value other derived
  rw [assumption_fixed, found] at present
  exact (Option.some.inj present).symm ▸ bound

end MicroCFTA.MinimumWitness
