import MicroCFTA.SourceObservations

/-!
# Actual identity and fresh-name invariants

The source allocates fresh names only for conflicting actual representatives.
The finite candidate stream below is proved long enough, distinct, and disjoint
from all observed and formula names. Ambiguity remains explicit at resolution.
-/
namespace MicroCFTA.SourceActuals
open SourceGuards SourceObservations

/-- Distinct source indices produce distinct reserved actual-value names. -/
theorem fresh_injective : Function.Injective (fun index : Nat => "__cfta_actual_" ++ toString index) := by
  intro left right equal
  exact Nat.repr_injective ((String.append_right_inj "__cfta_actual_").mp equal)

/-- The finite prefix contains no duplicate fresh-name candidates. -/
theorem candidates_nodup (count : Nat) :
    ((List.range count).map (fun index => "__cfta_actual_" ++ toString index)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.Pairwise.imp (fun apart same => apart (fresh_injective same)) List.nodup_range

/-- Every name belongs to exactly one side of a Boolean filter split. -/
theorem filter_length (items : List Name) (keep : Name → Bool) :
    (items.filter keep).length + (items.filter fun item => !keep item).length = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases found : keep item <;> simp [found] at * <;> omega

/-- The source stream always supplies as many fresh identities as conflicts require. -/
theorem fresh_length (avoid : List Name) (count : Nat) : (freshNames avoid count).length = count := by
  let candidates := (List.range (avoid.length + count)).map (fun index => "__cfta_actual_" ++ toString index)
  have unique := candidates_nodup (avoid.length + count)
  have rejectedUnique := List.Pairwise.filter (fun name => avoid.contains name) unique
  have rejectedBound : (candidates.filter fun name => avoid.contains name).length ≤ avoid.length := by
    apply List.Nodup.length_le_of_subset rejectedUnique
    intro name member
    simpa using (List.mem_filter.mp member).2
  have partition := filter_length candidates (fun name => avoid.contains name)
  have length : candidates.length = avoid.length + count := by simp [candidates]
  unfold freshNames
  rw [List.length_take]
  change min count (candidates.filter fun name => !avoid.contains name).length = count
  omega

/-- Every fresh identity differs from every other one in its allocation pass. -/
theorem fresh_nodup (avoid : List Name) (count : Nat) : (freshNames avoid count).Nodup :=
  (List.Pairwise.filter _ (candidates_nodup (avoid.length + count))).take

/-- Allocation never captures an observed constructor name or a formula free name. -/
theorem fresh_avoids (avoid : List Name) (count : Nat) (name : Name) (present : name ∈ freshNames avoid count) : name ∉ avoid := by
  have filtered := List.mem_of_mem_take present
  have kept := (List.mem_filter.mp filtered).2
  simpa using kept

/-- Every conflicting representative receives one declaration; zip truncation cannot drop one. -/
theorem allocated_length [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : SourceGuards.Guard Formula) :
    (allocated formulas observed sameAt guard).length = (conflicts observed sameAt guard).length := by
  simp [allocated, fresh_length]

/-- Every stored declaration target avoids all names that the source marks as used. -/
theorem allocated_avoids [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : SourceGuards.Guard Formula)
    (path : Path) (fresh original : Name) (present : (path, fresh, original) ∈ allocated formulas observed sameAt guard) :
    fresh ∉ usedNames formulas observed guard := by
  obtain ⟨pair, member, same⟩ := List.mem_map.mp present
  have freshPresent := (List.of_mem_zip member).2
  have equal : pair.2 = fresh := congrArg (fun entry : Path × Name × Name => entry.2.1) same
  exact fresh_avoids _ _ fresh (equal ▸ freshPresent)

/-- A successful substitution resolution proves that both source positions exist. -/
theorem resolve_exists (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (substitution : Substitution)
    (resolved : Resolved Formula) (success : resolve formulas observed fresh unknown substitution = some resolved) :
    ∃ actual formal, observed substitution.actual = some actual ∧ observed substitution.formal = some formal := by
  cases actual : observed substitution.actual with
  | none => simp [resolve, actual] at success
  | some value =>
      cases formal : observed substitution.formal with
      | none => simp [resolve, actual, formal] at success
      | some other => exact ⟨value, other, rfl, rfl⟩

/-- Literal symbol substitutions do not use solver-generated identity names. -/
theorem resolve_symbol (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (substitution : Substitution)
    (resolved : Resolved Formula) (actual formal : Observed Formula)
    (foundActual : observed substitution.actual = some actual) (foundFormal : observed substitution.formal = some formal)
    (success : resolve formulas observed fresh unknown substitution = some resolved) :
    resolved.symbolReplacement = (formal.name, actual.name) := by
  simp [resolve, foundActual, foundFormal] at success
  subst resolved
  rfl

/-- Ambiguous actual identity reaches the resolved scope unchanged. -/
theorem resolve_unknown (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (substitution : Substitution)
    (resolved : Resolved Formula) (success : resolve formulas observed fresh unknown substitution = some resolved) :
    resolved.identityKnown = false ↔ substitution.actual ∈ unknown := by
  obtain ⟨actual, formal, foundActual, foundFormal⟩ := resolve_exists formulas observed fresh unknown substitution resolved success
  simp [resolve, foundActual, foundFormal] at success
  subst resolved
  simp

/-- The recorded ambiguity set has exactly the source collision-and-unknown-identity witnesses. -/
theorem ambiguous_iff [DecidableEq Formula] (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (guard : SourceGuards.Guard Formula) (target : Path) :
    target ∈ ambiguous observed sameAt guard ↔
      ∃ actual ∈ actuals observed guard, actual.target = target ∧
        ∃ other ∈ actuals observed guard,
          actual.target ≠ other.target ∧ actual.name = other.name ∧ actual.refinement = other.refinement ∧
          sameAt actual.target other.target = none ∧
          ((observed actual.target).map Observed.leafness ≠ some .leaf ∨
            (observed other.target).map Observed.leafness ≠ some .leaf) := by
  simp only [ambiguous, List.mem_eraseDups, List.mem_map, List.mem_filter, List.any_eq_true,
    Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true_iff]
  constructor
  · rintro ⟨actual, ⟨member, other, present, ⟨⟨⟨⟨different, name⟩, refinement⟩, unknown⟩, shape⟩⟩, same⟩
    exact ⟨actual, member, same, other, present, different, name, refinement, unknown, shape⟩
  · rintro ⟨actual, member, same, other, present, different, name, refinement, unknown, shape⟩
    exact ⟨actual, ⟨member, other, present, ⟨⟨⟨⟨different, name⟩, refinement⟩, unknown⟩, shape⟩⟩, same⟩


/-- A finite formula fixture tests allocation and control without asserting solver semantics. -/
def fixtureFormulas : Formulas Nat :=
  ⟨fun _ value => value, id, fun _ => 0, fun _ _ => 0, fun _ => []⟩

/-- Two actual inner results have the same root name; formals and the requirement remain present. -/
def fixtureObservations : Observations Nat := fun path =>
  match path with
  | [0] | [1] => some ⟨"same", 0, .inner⟩
  | [2] => some ⟨"left", 0, .leaf⟩
  | [3] => some ⟨"right", 0, .leaf⟩
  | [4] => some ⟨"__cfta_actual_0", 0, .leaf⟩
  | _ => none

/-- The fixture substitutes two distinct actual paths into one semantic condition. -/
def fixtureGuard : SourceGuards.Guard Nat :=
  .substitute [⟨[0], [2]⟩, ⟨[1], [3]⟩] (.satisfies [4] 0)

/-- Allocation skips existing reserved-looking names and retains both conflicting identities. -/
theorem conflicting_inner_names :
    (substitutionValues fixtureFormulas fixtureObservations
      (sameShape fixtureFormulas fixtureObservations []) fixtureGuard).1 =
        [([0], "__cfta_actual_1", "same"), ([1], "__cfta_actual_2", "same")] ∧
    (substitutionValues fixtureFormulas fixtureObservations
      (sameShape fixtureFormulas fixtureObservations []) fixtureGuard).2 = [[0], [1]] := by
  have actualOrder : orderedPaths [[0], [1]] = [[0], [1]] := by
    change ([[0], [1]] : List Path).mergeSort _ = _
    exact List.mergeSort_of_pairwise (by decide +kernel)
  have usedOrder : orderedPaths [[0], [2], [1], [3], [4]] = [[0], [1], [2], [3], [4]] := by
    change ([[0], [2], [1], [3], [4]] : List Path).mergeSort _ = _
    simp [List.mergeSort, compare, List.compareLex, compareOfLessAndEq]
  simp [fixtureGuard, substitutionValues, actuals, actualPaths, allocated, conflicts, values,
    usedNames, paths, requirements, ambiguous, actualOrder, usedOrder]
  decide +kernel

/-- The actual sparse evaluator does not turn an identity-ambiguous solver No into a dropped candidate. -/
theorem ambiguous_refutation_remains_unknown :
    evaluateGuardWithShape fixtureFormulas (fun _ _ _ => .no) fixtureObservations fixtureGuard = .unknown := by
  unfold evaluateGuardWithShape evaluateGuardWithSame
  rw [show (substitutionValues fixtureFormulas fixtureObservations
    (sameShape fixtureFormulas fixtureObservations []) fixtureGuard) =
      ([([0], "__cfta_actual_1", "same"), ([1], "__cfta_actual_2", "same")], [[0], [1]]) from
        Prod.ext conflicting_inner_names.1 conflicting_inner_names.2]
  simp [fixtureGuard, evaluateWith, resolveMany, resolve, fixtureObservations, fixtureFormulas,
    decideWith]


/-- Repeated uses of one actual path share one identity and need no fresh declaration. -/
theorem repeated_actual_has_one_identity :
    (substitutionValues fixtureFormulas fixtureObservations
      (sameShape fixtureFormulas fixtureObservations [])
      (.substitute [⟨[0], [2]⟩, ⟨[0], [3]⟩] (.satisfies [4] 0))).1 = [] ∧
    (substitutionValues fixtureFormulas fixtureObservations
      (sameShape fixtureFormulas fixtureObservations [])
      (.substitute [⟨[0], [2]⟩, ⟨[0], [3]⟩] (.satisfies [4] 0))).2 = [] := by
  have actualOrder : orderedPaths [[0], [0]] = [[0]] := by
    change ([[0]] : List Path).mergeSort _ = _
    exact List.mergeSort_of_pairwise (by decide +kernel)
  simp only [substitutionValues, actuals, actualPaths, allocated, conflicts, values,
    usedNames, paths, requirements, ambiguous, List.map_cons, List.map_nil, List.append_nil,
    actualOrder]
  decide +kernel

end MicroCFTA.SourceActuals
