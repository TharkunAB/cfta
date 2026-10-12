import MicroCFTA.GuardConjunction
import MicroCFTA.EqualityNormalize

/-!
# Global actual tables survive conjunction normalization

Conjunction normalization changes list order and multiplicity. The source
path sets, ordered actuals, and finite fresh-name streams remain exact.
-/
namespace MicroCFTA.GuardConjunctionNames
open SourceGuards GuardConjunction

private theorem atoms_projection (projection : Guard Formula → List α)
    (top : projection .top = []) (andParts : ∀ parts, projection (.and parts) = parts.flatMap projection)
    (guard : Guard Formula) (item : α) : item ∈ (atoms guard).flatMap projection ↔ item ∈ projection guard := by
  cases guard with
  | top => simp only [atoms, top, List.flatMap_nil]
  | and parts =>
      rw [atoms, andParts]
      constructor
      · rintro member
        obtain ⟨atom, ⟨part, present, atomMember⟩, value⟩ :=
          (by simpa only [List.mem_flatMap] using member : ∃ atom, (∃ part, part ∈ parts ∧ atom ∈ atoms part) ∧ item ∈ projection atom)
        exact List.mem_flatMap.mpr ⟨part, present, (atoms_projection projection top andParts part item).mp
          (List.mem_flatMap.mpr ⟨atom, atomMember, value⟩)⟩
      · rintro member
        obtain ⟨part, present, value⟩ := List.mem_flatMap.mp member
        obtain ⟨atom, atomMember, value⟩ := List.mem_flatMap.mp ((atoms_projection projection top andParts part item).mpr value)
        exact List.mem_flatMap.mpr ⟨atom, List.mem_flatMap.mpr ⟨part, present, atomMember⟩, value⟩
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => simp only [atoms, List.flatMap_singleton]
termination_by sizeOf guard

private theorem conjoin_projection (projection : Guard Formula → List α)
    (top : projection .top = []) (andParts : ∀ parts, projection (.and parts) = parts.flatMap projection)
    (guards : List (Guard Formula)) : projection (conjoin guards) = guards.flatMap projection := by
  cases guards with
  | nil => exact top
  | cons first rest => cases rest with
    | nil => simp only [conjoin, List.flatMap_singleton]
    | cons second rest => exact andParts _

/-- Any source footprint which unions outer conjunctions keeps exactly its members. -/
theorem projection_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (projection : Guard Formula → List α)
    (top : projection .top = []) (andParts : ∀ parts, projection (.and parts) = parts.flatMap projection)
    (guard : Guard Formula) (item : α) : item ∈ projection (normalize le guard) ↔ item ∈ projection guard := by
  rw [normalize, conjoin_projection projection top andParts]
  simp only [List.mem_flatMap, canonical_mem]
  simpa only [List.mem_flatMap] using atoms_projection projection top andParts guard item

theorem paths_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) (path : Path) :
    path ∈ paths (normalize le guard) ↔ path ∈ paths guard :=
  projection_mem le paths (by simp [paths]) (by intro parts; simp [paths]) guard path

theorem actualPaths_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) (path : Path) :
    path ∈ actualPaths (normalize le guard) ↔ path ∈ actualPaths guard :=
  projection_mem le actualPaths (by simp [actualPaths]) (by intro parts; simp [actualPaths]) guard path

theorem sensitive_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) (path : Path) :
    path ∈ sensitive (normalize le guard) ↔ path ∈ sensitive guard :=
  projection_mem le sensitive (by simp [sensitive]) (by intro parts; simp [sensitive]) guard path

theorem requirements_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) (formula : Formula) :
    formula ∈ requirements (normalize le guard) ↔ formula ∈ requirements guard :=
  projection_mem le requirements (by simp [requirements]) (by intro parts; simp [requirements]) guard formula

private theorem compare_path (left right : Path) : (compare left right != .gt) = decide (left ≤ right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq]
  induction left generalizing right with
  | nil => cases right <;> simp [compare, List.compareLex]
  | cons a rest ih =>
      cases right with
      | nil => simp [compare, List.compareLex]
      | cons b tail =>
          by_cases less : a < b
          · simp [compare, List.compareLex, compareOfLessAndEq, less, List.cons_le_cons_iff] <;> omega
          · by_cases same : a = b
            · subst b
              simpa [compare, List.compareLex, compareOfLessAndEq, List.cons_le_cons_iff] using ih tail
            · simp [compare, List.compareLex, compareOfLessAndEq, less, same, List.cons_le_cons_iff] <;> omega

/-- Ascending source path sets depend only on membership. -/
theorem orderedPaths_ext (first second : List Path) (same : ∀ path, path ∈ first ↔ path ∈ second) :
    orderedPaths first = orderedPaths second := by
  have canonical : ∀ paths, orderedPaths paths = EqualityNormalize.canonicalClass paths := by
    intro paths
    simp only [orderedPaths, EqualityNormalize.canonicalClass]
    congr 1
    funext left right
    exact compare_path left right
  rw [canonical, canonical]
  exact EqualityNormalize.canonicalClass_ext first second same

private theorem freshNames_ext_le (first second : List Name) (count : Nat)
    (same : ∀ name, name ∈ first ↔ name ∈ second) (length : first.length ≤ second.length) :
    freshNames first count = freshNames second count := by
  have keep : (fun name => !first.contains name) = (fun name => !second.contains name) := by
    funext name
    have equal : first.contains name = second.contains name := Bool.eq_iff_iff.mpr (by simpa using same name)
    rw [equal]
  have prefixLength := SourceActuals.fresh_length first count
  unfold freshNames at prefixLength ⊢
  rw [List.length_take] at prefixLength
  have enough : count ≤ (((List.range (first.length + count)).map (fun index => "__microcfta_actual_" ++ toString index)).filter
      (fun candidate => !first.contains candidate)).length := by omega
  have longer : second.length + count = (first.length + count) + (second.length - first.length) := by omega
  rw [longer]
  conv => rhs; rw [List.range_add, List.map_append, List.filter_append, ← keep, List.take_append_of_le_length enough]

/-- Avoid-list order and multiplicity cannot change the executed finite fresh-name stream. -/
theorem freshNames_ext (first second : List Name) (count : Nat) (same : ∀ name, name ∈ first ↔ name ∈ second) :
    freshNames first count = freshNames second count := by
  by_cases length : first.length ≤ second.length
  · exact freshNames_ext_le first second count same length
  · exact (freshNames_ext_le second first count (fun name => (same name).symm) (by omega)).symm

/-- Normalization retains the exact source order of requested paths. -/
theorem ordered_paths [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) :
    orderedPaths (paths (normalize le guard)) = orderedPaths (paths guard) :=
  orderedPaths_ext _ _ (paths_mem le guard)

/-- Actual path enumeration retains its exact order and length. -/
theorem ordered_actuals [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) (guard : Guard Formula) :
    orderedPaths (actualPaths (normalize le guard)) = orderedPaths (actualPaths guard) :=
  orderedPaths_ext _ _ (actualPaths_mem le guard)

/-- The executed source actual table is identical after conjunction normalization. -/
theorem actuals_normalize [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (observed : Observations Formula) (guard : Guard Formula) : actuals observed (normalize le guard) = actuals observed guard := by
  simp only [actuals, ordered_actuals le guard]

/-- Source representative/name values retain their order and multiplicity policy. -/
theorem values_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (observed : Observations Formula) (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    values observed sameAt (normalize le guard) = values observed sameAt guard := by
  simp only [values, actuals_normalize le observed guard]

/-- The source count-based conflict list is unchanged. -/
theorem conflicts_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (observed : Observations Formula) (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    conflicts observed sameAt (normalize le guard) = conflicts observed sameAt guard := by
  simp only [conflicts, values_normalize le observed sameAt guard]

/-- The global ambiguity list and the conservative source gate are unchanged. -/
theorem ambiguous_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (observed : Observations Formula) (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    ambiguous observed sameAt (normalize le guard) = ambiguous observed sameAt guard := by
  simp only [ambiguous, actuals_normalize le observed guard]

/-- Requirement reordering can change the avoid list, but cannot change its membership. -/
theorem usedNames_mem [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula) (name : Name) :
    name ∈ usedNames formulas observed (normalize le guard) ↔ name ∈ usedNames formulas observed guard := by
  simp only [usedNames, ordered_paths le guard, List.mem_append, List.mem_flatMap, requirements_mem le guard]

/-- The actual allocation rows remain identical despite reordered or repeated requirement names. -/
theorem allocated_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (observed : Observations Formula) (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    allocated formulas observed sameAt (normalize le guard) = allocated formulas observed sameAt guard := by
  simp only [allocated, conflicts_normalize le observed sameAt guard]
  rw [freshNames_ext _ _ _ (usedNames_mem le formulas observed guard)]

/-- Both global source tables are exactly equal before any nested scope is resolved. -/
theorem substitutionValues_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (formulas : Formulas Formula) (observed : Observations Formula) (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    substitutionValues formulas observed sameAt (normalize le guard) = substitutionValues formulas observed sameAt guard := by
  simp only [substitutionValues, actuals_normalize le observed guard, allocated_normalize le formulas observed sameAt guard,
    ambiguous_normalize le observed sameAt guard]

/-- The full public source evaluator, including its global allocation pass, is invariant under normalization. -/
theorem evaluateGuardWithSame_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool) (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool) (guard : Guard Formula) :
    evaluateGuardWithSame formulas solver observed sameAt (normalize le guard) = evaluateGuardWithSame formulas solver observed sameAt guard := by
  unfold evaluateGuardWithSame
  rw [substitutionValues_normalize le formulas observed (sameAt []) guard]
  exact normalize_evaluate le formulas solver observed sameAt _ _ [] true guard

/-- Complete-term evaluation retains all verdicts without requiring solver name stability. -/
theorem evaluateGuard_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool) (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Language.Term (SourceObservations.Label Formula)) :
    SourceObservations.evaluateGuard formulas solver (normalize le guard) term = SourceObservations.evaluateGuard formulas solver guard term :=
  evaluateGuardWithSame_normalize le formulas solver (SourceObservations.observe term) (SourceObservations.sameTerm formulas term) guard

/-- Sparse evaluation retains all verdicts with the same exact allocated names. -/
theorem evaluateGuardWithShape_normalize [DecidableEq Formula] [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool) (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (guard : Guard Formula) :
    SourceObservations.evaluateGuardWithShape formulas solver observed (normalize le guard) =
      SourceObservations.evaluateGuardWithShape formulas solver observed guard :=
  evaluateGuardWithSame_normalize le formulas solver observed (SourceObservations.sameShape formulas observed) guard

end MicroCFTA.GuardConjunctionNames
