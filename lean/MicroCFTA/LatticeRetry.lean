import MicroCFTA.LatticeSelect

/-!
# Named elimination errors and bounded order retries

The source reports the name at the failed elimination index. A non-unit
coefficient moves that name to the first position. The retry budget decreases
at each move. Successful counts keep their meaning in every coordinate order.
-/

namespace MicroCFTA.LatticeRetry
open LatticeLinear LatticePiece LatticePipeline LatticeCount LatticeLevels
open LatticeFormula LatticeInput LatticeAPI

/-- Eliminate the declared names in reverse order and retain the failed name. -/
def namedLevels : (reverseNames : List Name) → (pieces : List Piece) →
    (∀ piece ∈ pieces, ValidPiece piece) → Except (Name × SplitError) (List (List Piece))
  | [], pieces, _ => .ok [pieces]
  | name :: rest, pieces, valid =>
    match next : eliminate rest.length pieces valid with
    | .error error => .error (name, error)
    | .ok output =>
      match namedLevels rest output (eliminate_valid rest.length pieces valid output next) with
      | .error error => .error error
      | .ok levels => .ok (levels ++ [pieces])

/-- Erasing the diagnostic name gives the checked numeric elimination exactly. -/
theorem namedLevels_erases (reverseNames : List Name) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) :
    (namedLevels reverseNames pieces valid).mapError Prod.snd =
      buildLevels reverseNames.length pieces valid := by
  induction reverseNames generalizing pieces with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.length_cons, namedLevels, buildLevels]
    split
    · next error found =>
      split
      · next other chosen =>
        have same := Except.error.inj (found.symm.trans chosen)
        cases same
        rfl
      · next output chosen => rw [found] at chosen; cases chosen
    · next output found =>
      have previous := ih output (eliminate_valid rest.length pieces valid output found)
      split
      · next error nested =>
        simp [nested, Except.mapError] at previous
        split
        · next other chosen => rw [found] at chosen; cases chosen
        · next other chosen =>
          have same := Except.ok.inj (chosen.symm.trans found)
          subst other
          rw [← previous]
          rfl
      · next levels nested =>
        simp [nested, Except.mapError] at previous
        split
        · next other chosen => rw [found] at chosen; cases chosen
        · next other chosen =>
          have same := Except.ok.inj (chosen.symm.trans found)
          subst other
          rw [← previous]
          rfl

/-- Every reported elimination name belongs to the declaration list. -/
theorem namedLevels_error_mem (reverseNames : List Name) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece) (name : Name) (error : SplitError)
    (failed : namedLevels reverseNames pieces valid = .error (name, error)) :
    name ∈ reverseNames := by
  induction reverseNames generalizing pieces with
  | nil => simp [namedLevels] at failed
  | cons head rest ih =>
    unfold namedLevels at failed
    split at failed
    · cases failed; exact List.mem_cons_self
    · next output found =>
      split at failed
      · next failure nested =>
        cases failed
        exact List.mem_cons_of_mem head (ih output _ nested)
      · cases failed

/-- Source errors retain the variable name on elimination failures. -/
inductive NamedError (Name : Type) where
  | formula (error : LatticeFormula.Error Name)
  | elimination (name : Name) (error : SplitError)
  | nonintegral

/-- Remove the source diagnostic name without changing the error class. -/
def eraseError : NamedError Name → LatticeAPI.Error Name
  | .formula error => .formula error
  | .elimination _ error => .elimination error
  | .nonintegral => .nonintegral

/-- Compile the point table with the source's named elimination errors. -/
def namedPoints [DecidableEq Name] (names : List Name) (formula : Formula Name) :
    Except (NamedError Name) Points :=
  match signed (variableOf names) true formula with
  | .error error => .error (.formula error)
  | .ok compiled =>
    match namedLevels names.reverse (initial compiled) (initial_valid compiled) with
    | .error (name, error) => .error (.elimination name error)
    | .ok levels =>
      let value := polynomialCount (levels.getD 0 [])
      if value.den = 1 then .ok ⟨names.length, levels, value.num⟩ else .error .nonintegral

/-- Named compilation has the same success value and error class as point compilation. -/
theorem namedPoints_erases [DecidableEq Name] (names : List Name) (formula : Formula Name) :
    (namedPoints names formula).mapError eraseError = points names formula := by
  unfold namedPoints points
  cases parsed : signed (variableOf names) true formula with
  | error error => rfl
  | ok compiled =>
    have erased := namedLevels_erases names.reverse (initial compiled) (initial_valid compiled)
    simp only [List.length_reverse] at erased
    cases built : namedLevels names.reverse (initial compiled) (initial_valid compiled) with
    | error failure =>
      simp [built, Except.mapError] at erased
      simp [built, ← erased, Except.mapError, eraseError]
    | ok levels =>
      simp [built, Except.mapError] at erased
      simp only [built, ← erased]
      split <;> rfl

/-- A successful named table is a successful checked point table. -/
theorem namedPoints_success [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (result : Points) (success : namedPoints names formula = .ok result) :
    points names formula = .ok result := by
  rw [← namedPoints_erases, success]
  rfl

/-- An elimination failure can move only a declared variable. -/
theorem namedPoints_error_mem [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (name : Name) (error : SplitError)
    (failed : namedPoints names formula = .error (.elimination name error)) : name ∈ names := by
  unfold namedPoints at failed
  split at failed
  · cases failed
  · next compiled parsed =>
    split at failed
    · next failedName failedError built =>
      cases failed
      exact List.mem_reverse.mp (namedLevels_error_mem names.reverse _ _ name error built)
    · dsimp only at failed; split at failed <;> cases failed

/-- Move the failed variable to the position eliminated last. -/
def moveFirst [DecidableEq Name] (name : Name) (names : List Name) : List Name :=
  name :: names.filter (fun other => decide (other ≠ name))

/-- Moving a declared name preserves the complete distinct declaration list. -/
theorem moveFirst_perm [DecidableEq Name] (name : Name) (names : List Name)
    (unique : names.Nodup) (member : name ∈ names) : names.Perm (moveFirst name names) := by
  induction names with
  | nil => simp at member
  | cons head rest ih =>
    have distinct := List.nodup_cons.mp unique
    by_cases same : head = name
    · subst head
      have unchanged : rest.filter (fun other => decide (other ≠ name)) = rest := by
        apply List.filter_eq_self.mpr
        intro other belongs
        simp only [decide_eq_true_eq]
        intro equal
        subst other
        exact distinct.1 belongs
      simp only [moveFirst, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rw [unchanged]
    · have belongs : name ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have previous := (ih distinct.2 belongs).cons head
      simp only [moveFirst, List.filter_cons, decide_eq_true_eq] at previous ⊢
      rw [ite_eq_left same]
      exact previous.trans (List.Perm.swap _ _ _)

/-- Retry only the source non-unit failure, with at most the supplied number of moves. -/
def attempt [DecidableEq Name] : Nat → List Name → Formula Name → Except (NamedError Name) Points
  | 0, names, formula => namedPoints names formula
  | tries + 1, names, formula =>
    match namedPoints names formula with
    | .error (.elimination name .nonUnitCoefficient) =>
      if names.take 1 ≠ [name] then attempt tries (moveFirst name names) formula
      else .error (.elimination name .nonUnitCoefficient)
    | result => result

/-- A retry result is the actual query result in a permutation of the original order. -/
theorem attempt_origin [DecidableEq Name] (tries : Nat) (names : List Name) (formula : Formula Name)
    (unique : names.Nodup) (result : Except (NamedError Name) Points)
    (completed : attempt tries names formula = result) :
    ∃ finalOrder, names.Perm finalOrder ∧ namedPoints finalOrder formula = result := by
  induction tries generalizing names with
  | zero => exact ⟨names, .rfl, completed⟩
  | succ tries ih =>
    cases queried : namedPoints names formula with
    | ok table => exact ⟨names, .rfl, by simpa [attempt, queried] using completed⟩
    | error error =>
      cases error with
      | formula error => exact ⟨names, .rfl, by simpa [attempt, queried] using completed⟩
      | nonintegral => exact ⟨names, .rfl, by simpa [attempt, queried] using completed⟩
      | elimination name error =>
        cases error with
        | unboundedVariable => exact ⟨names, .rfl, by simpa [attempt, queried] using completed⟩
        | nonUnitCoefficient =>
          by_cases move : names.take 1 ≠ [name]
          · have reordered := moveFirst_perm name names unique
              (namedPoints_error_mem names formula name .nonUnitCoefficient queried)
            have next : attempt tries (moveFirst name names) formula = result := by
              simpa only [attempt, queried, ite_eq_left move] using completed
            obtain ⟨finalOrder, permutation, returned⟩ := ih (moveFirst name names) (reordered.nodup unique) next
            exact ⟨finalOrder, reordered.trans permutation, returned⟩
          · exact ⟨names, .rfl, by simpa [attempt, queried, move] using completed⟩

/-- The retry loop cannot return the unreachable nonintegral-count failure. -/
theorem attempt_ne_nonintegral [DecidableEq Name] (tries : Nat) (names : List Name) (formula : Formula Name)
    (unique : names.Nodup) : attempt tries names formula ≠ .error .nonintegral := by
  intro failed
  obtain ⟨order, _, final⟩ := attempt_origin tries names formula unique _ failed
  have erased := namedPoints_erases order formula
  rw [final] at erased
  exact points_ne_nonintegral order formula erased.symm

/-- A successful retry has an exact count in its final coordinate order. -/
theorem attempt_success [DecidableEq Name] (tries : Nat) (names : List Name) (formula : Formula Name)
    (unique : names.Nodup) (result : Points) (completed : attempt tries names formula = .ok result) :
    ∃ finalOrder, names.Perm finalOrder ∧ points finalOrder formula = .ok result := by
  obtain ⟨order, permutation, final⟩ := attempt_origin tries names formula unique _ completed
  exact ⟨order, permutation, namedPoints_success order formula result final⟩

/-- Zero count after retries still means that there is no named integer solution. -/
theorem attempt_zero_iff [DecidableEq Name] (tries : Nat) (names : List Name) (formula : Formula Name)
    (unique : names.Nodup) (result : Points) (completed : attempt tries names formula = .ok result) :
    result.count = 0 ↔ ∀ values : Name → Int, evaluateFormula values formula ≠ some true := by
  obtain ⟨order, _, final⟩ := attempt_success tries names formula unique result completed
  exact points_zero_iff_named order formula result final

/-- Successful retries retain the complete point decoder and its distinct finite ranks. -/
theorem attempt_api_exact (tries : Nat) (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (unique : names.Nodup) (result : Points)
    (completed : attempt tries names (FullSyntax.lowerFormula formula) = .ok result) :
    ∃ finalOrder, names.Perm finalOrder ∧
      result.count.toNat = LatticeSelect.pointCount result.levels ∧ result.dimension = names.length ∧
      (∀ tuple, (tuple.length = names.length ∧ FullSyntax.Holds FullSyntax.integerModel
          (nameValues finalOrder (LatticeSelect.assignTuple (fun _ => 0) 0 tuple)) formula) ↔
        ∃ rank : Fin (LatticeSelect.pointCount result.levels),
          LatticeSelect.decode result.dimension result.levels rank = tuple) ∧
      Function.Injective (LatticeSelect.decode result.dimension result.levels) := by
  obtain ⟨order, permutation, success⟩ := attempt_success tries names _ unique result completed
  refine ⟨order, permutation, ?_⟩
  simpa only [← permutation.length_eq] using LatticeSelect.points_api_exact order formula result success

/-- The source makes at most one retry per initial variable. Errors remain unknown. -/
def implication [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name) : Verdict :=
  match attempt names.length names (counterexamples premise conclusion) with
  | .error _ => .unknown
  | .ok result => if result.count = 0 then .yes else .no

/-- Every definite verdict is the exact verdict of a successful coordinate order. -/
theorem implication_origin [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (unique : names.Nodup) (verdict : Verdict) (definite : verdict ≠ .unknown)
    (returned : implication names premise conclusion = verdict) :
    ∃ finalOrder, names.Perm finalOrder ∧ LatticeAPI.implication finalOrder premise conclusion = verdict := by
  cases completed : attempt names.length names (counterexamples premise conclusion) with
  | error error => simp [implication, completed] at returned; exact False.elim (definite returned.symm)
  | ok result =>
    obtain ⟨order, permutation, success⟩ := attempt_success names.length names _ unique result completed
    exact ⟨order, permutation, by simpa [implication, completed, LatticeAPI.implication, success] using returned⟩

/-- Retry-based Yes excludes all integer counterexamples. -/
theorem implication_yes [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (unique : names.Nodup) (returned : implication names premise conclusion = .yes) :
    ∀ values : Name → Int, evaluateFormula values premise = some true → evaluateFormula values conclusion = some true := by
  obtain ⟨order, _, yes⟩ := implication_origin names premise conclusion unique .yes (by decide) returned
  exact LatticeAPI.implication_yes order premise conclusion yes

/-- Retry-based No supplies an integer counterexample. -/
theorem implication_no [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (unique : names.Nodup) (returned : implication names premise conclusion = .no) :
    ∃ values : Name → Int, evaluateFormula values premise = some true ∧ evaluateFormula values conclusion ≠ some true := by
  obtain ⟨order, _, no⟩ := implication_origin names premise conclusion unique .no (by decide) returned
  exact LatticeAPI.implication_no order premise conclusion no

end MicroCFTA.LatticeRetry
