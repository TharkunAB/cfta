import MicroCFTA.LatticeDecision
import MicroCFTA.LatticeLevels

/-!
# Point-count constructor and implication decisions

The constructor parses a formula, stores the source elimination levels, and
reads the numerator of their final constant sum. The integral check's failure
branch is represented explicitly and proved unreachable after successful
parsing and elimination. Machine-sized dimensions and typed syntax translation
remain separate representation obligations.
-/

namespace MicroCFTA.LatticeAPI
open LatticeLinear LatticeSigned LatticeFormula LatticeInput LatticeCount LatticeLevels

/-- Stored levels and direct elimination compute the same final piece list. -/
theorem buildLevels_sumOut (dimension : Nat) (pieces : List LatticePiece.Piece)
    (valid : ∀ piece ∈ pieces, LatticePiece.ValidPiece piece)
    (levels : List (List LatticePiece.Piece)) (built : buildLevels dimension pieces valid = .ok levels) :
    sumOut (List.range dimension).reverse pieces valid = .ok (levels.getD 0 []) := by
  induction dimension generalizing pieces levels with
  | zero => simp [buildLevels] at built; cases built; rfl
  | succ dimension ih =>
    unfold buildLevels at built
    split at built
    · cases built
    · next nextPieces found =>
      split at built
      · cases built
      · next previous earlier =>
        cases built
        have length := buildLevels_length dimension nextPieces _ previous earlier
        rw [getD_append_left previous [pieces] [] 0 (by omega)]
        have order : (List.range (dimension + 1)).reverse = dimension :: (List.range dimension).reverse := by
          simp [List.range_succ, List.reverse_append]
        rw [order]
        unfold sumOut
        split
        · next rejected => rw [found] at rejected; cases rejected
        · next actual chosen =>
          have same : actual = nextPieces := Except.ok.inj (chosen.symm.trans found)
          subst actual
          exact ih nextPieces _ previous earlier

/-- The public point table retains the dimension, all levels, and the integer count. -/
structure Points where
  dimension : Nat
  levels : List (List LatticePiece.Piece)
  count : Int

/-- Supported-fragment errors and the explicit internal integral check. -/
inductive Error (Name : Type) where
  | formula (error : LatticeFormula.Error Name)
  | elimination (error : LatticePiece.SplitError)
  | nonintegral

/-- Execute the source point-count constructor through its integral check. -/
def points [DecidableEq Name] (names : List Name) (formula : Formula Name) : Except (Error Name) Points :=
  match signed (variableOf names) true formula with
  | .error error => .error (.formula error)
  | .ok compiled =>
    match buildLevels names.length (initial compiled) (initial_valid compiled) with
    | .error error => .error (.elimination error)
    | .ok levels =>
      let value := polynomialCount (levels.getD 0 [])
      if value.den = 1 then .ok ⟨names.length, levels, value.num⟩ else .error .nonintegral

/-- Successful parsing and stored elimination always pass the source integral check. -/
theorem points_of_build [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (levels : List (List LatticePiece.Piece))
    (built : buildLevels names.length (initial compiled) (initial_valid compiled) = .ok levels) :
    points names formula = .ok ⟨names.length, levels, (polynomialCount (levels.getD 0 [])).num⟩ := by
  have integral := LatticeDecision.count_integral names formula compiled parsed _
    (buildLevels_sumOut names.length (initial compiled) (initial_valid compiled) levels built)
  simp [points, parsed, built]
  exact integral.1

/-- The source's internal nonintegral-count error is unreachable. -/
theorem points_ne_nonintegral [DecidableEq Name] (names : List Name) (formula : Formula Name) :
    points names formula ≠ .error .nonintegral := by
  cases parsed : signed (variableOf names) true formula with
  | error error => simp [points, parsed]
  | ok compiled =>
    cases built : buildLevels names.length (initial compiled) (initial_valid compiled) with
    | error error => simp [points, parsed, built]
    | ok levels => rw [points_of_build names formula compiled parsed levels built]; simp

/-- Successful tables come from the actual parsed formula and stored elimination. -/
theorem points_success [DecidableEq Name] (names : List Name) (formula : Formula Name) (result : Points)
    (success : points names formula = .ok result) :
    ∃ compiled : Checked, signed (variableOf names) true formula = .ok compiled ∧
      buildLevels names.length (initial compiled) (initial_valid compiled) = .ok result.levels ∧
      result.dimension = names.length ∧ result.count = (polynomialCount (result.levels.getD 0 [])).num := by
  cases parsed : signed (variableOf names) true formula with
  | error error => simp [points, parsed] at success
  | ok compiled =>
    cases built : buildLevels names.length (initial compiled) (initial_valid compiled) with
    | error error => simp [points, parsed, built] at success
    | ok levels =>
      rw [points_of_build names formula compiled parsed levels built] at success
      cases success
      exact ⟨compiled, rfl, built, rfl, rfl⟩

/-- The stored integer count equals the exact rational sum and is nonnegative. -/
theorem points_count [DecidableEq Name] (names : List Name) (formula : Formula Name) (result : Points)
    (success : points names formula = .ok result) :
    (result.count : Rat) = polynomialCount (result.levels.getD 0 []) ∧ 0 ≤ result.count := by
  obtain ⟨compiled, parsed, built, _, countEq⟩ := points_success names formula result success
  obtain ⟨count, exactCount⟩ := count_natural names formula compiled parsed _
    (buildLevels_sumOut names.length (initial compiled) (initial_valid compiled) result.levels built)
  rw [countEq, exactCount]
  exact ⟨rfl, Int.natCast_nonneg count⟩

/-- A returned point table has zero count exactly when its formula has no integer solution. -/
theorem points_zero_iff [DecidableEq Name] (names : List Name) (formula : Formula Name) (result : Points)
    (success : points names formula = .ok result) :
    result.count = 0 ↔ ∀ assignment, evaluateFormula (nameValues names assignment) formula ≠ some true := by
  obtain ⟨compiled, parsed, built, _, countEq⟩ := points_success names formula result success
  obtain ⟨count, exactCount⟩ := count_natural names formula compiled parsed _
    (buildLevels_sumOut names.length (initial compiled) (initial_valid compiled) result.levels built)
  have zero := LatticeDecision.count_zero_iff names formula compiled parsed _
    (buildLevels_sumOut names.length (initial compiled) (initial_valid compiled) result.levels built)
  rw [countEq, exactCount]
  rw [exactCount] at zero
  simpa using zero

/-- The formula counted by source implication checking. -/
def counterexamples (premise conclusion : Formula Name) : Formula Name := .conj premise (.neg conclusion)

/-- Defined counterexample evaluation rejects exactly valid implication assignments. -/
theorem counterexamples_false_iff (names : Name → Int) (premise conclusion : Formula Name)
    (defined : ∃ value, evaluateFormula names (counterexamples premise conclusion) = some value) :
    evaluateFormula names (counterexamples premise conclusion) ≠ some true ↔
      (evaluateFormula names premise = some true → evaluateFormula names conclusion = some true) := by
  cases hp : evaluateFormula names premise <;> cases hc : evaluateFormula names conclusion <;>
    simp [counterexamples, evaluateFormula, hp, hc] at defined ⊢

/-- The final decisions used by lattice entailment. -/
inductive Verdict where
  | yes | no | unknown
  deriving DecidableEq

/-- Count integer counterexamples and preserve unsupported-input uncertainty. -/
def implication [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name) : Verdict :=
  match points names (counterexamples premise conclusion) with
  | .error _ => .unknown
  | .ok result => if result.count = 0 then .yes else .no

/-- Every successful point compilation decides exactly the integer implication. -/
theorem implication_iff [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (result : Points) (success : points names (counterexamples premise conclusion) = .ok result) :
    implication names premise conclusion = .yes ↔
      ∀ assignment, evaluateFormula (nameValues names assignment) premise = some true →
        evaluateFormula (nameValues names assignment) conclusion = some true := by
  have zero := points_zero_iff names (counterexamples premise conclusion) result success
  obtain ⟨compiled, parsed, _, _, _⟩ := points_success names (counterexamples premise conclusion) result success
  have defined : ∀ assignment, ∃ value,
      evaluateFormula (nameValues names assignment) (counterexamples premise conclusion) = some value := by
    intro assignment
    obtain ⟨value, evaluated, _⟩ := signed_indicator (variableOf names) (nameValues names assignment) assignment
      (nameValues_correct names assignment) (counterexamples premise conclusion) compiled parsed
    exact ⟨value, evaluated⟩
  simp only [implication, success]
  have verdict : (if result.count = 0 then Verdict.yes else Verdict.no) = .yes ↔ result.count = 0 := by
    by_cases empty : result.count = 0 <;> simp [empty]
  rw [verdict, zero]
  exact forall_congr' (fun assignment => counterexamples_false_iff _ premise conclusion (defined assignment))

/-- The first matching name index retrieves that same name from the declaration list. -/
theorem variableOf_lookup [DecidableEq Name] (names : List Name) (name : Name) (index : Nat)
    (found : variableOf names name = some index) : names[index]? = some name := by
  induction names generalizing index with
  | nil => simp [variableOf] at found
  | cons first rest ih =>
    by_cases same : name = first
    · simp [variableOf, same] at found
      subst index
      simp [same]
    · cases tail : variableOf rest name with
      | none => simp [variableOf, same, tail] at found
      | some previous =>
        simp [variableOf, same, tail] at found
        subst index
        exact ih previous tail

/-- Convert an arbitrary named valuation to the constructor's coordinate order. -/
def coordinateValues (names : List Name) (values : Name → Int) (index : Nat) : Int :=
  (names[index]?.map values).getD 0

/-- Coordinate conversion preserves every declared name, including repeated declarations. -/
theorem coordinateValues_correct [DecidableEq Name] (names : List Name) (values : Name → Int)
    (name : Name) (index : Nat) (found : variableOf names name = some index) :
    values name = coordinateValues names values index := by
  simp [coordinateValues, variableOf_lookup names name index found]

/-- A successfully parsed formula has the same named and coordinate interpretations. -/
theorem formula_named [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (values : Name → Int) :
    evaluateFormula values formula =
      evaluateFormula (nameValues names (coordinateValues names values)) formula := by
  obtain ⟨left, leftValue, leftScore⟩ := signed_indicator (variableOf names) values (coordinateValues names values)
    (coordinateValues_correct names values) formula compiled parsed
  obtain ⟨right, rightValue, rightScore⟩ := signed_indicator (variableOf names)
    (nameValues names (coordinateValues names values)) (coordinateValues names values)
    (nameValues_correct names _) formula compiled parsed
  rw [leftValue, rightValue]
  have equal : left = right := by
    cases left <;> cases right <;> simp_all
  exact congrArg some equal

/-- Zero count is independent of coordinate order and means no named integer valuation satisfies the formula. -/
theorem points_zero_iff_named [DecidableEq Name] (names : List Name) (formula : Formula Name) (result : Points)
    (success : points names formula = .ok result) :
    result.count = 0 ↔ ∀ values : Name → Int, evaluateFormula values formula ≠ some true := by
  rw [points_zero_iff names formula result success]
  obtain ⟨compiled, parsed, _, _, _⟩ := points_success names formula result success
  constructor
  · intro noCoordinate values trueValue
    rw [formula_named names formula compiled parsed values] at trueValue
    exact noCoordinate (coordinateValues names values) trueValue
  · exact fun noNamed assignment => noNamed (nameValues names assignment)

/-- Successful implication checking is exact over all named integer valuations. -/
theorem implication_named_iff [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (result : Points) (success : points names (counterexamples premise conclusion) = .ok result) :
    implication names premise conclusion = .yes ↔
      ∀ values : Name → Int, evaluateFormula values premise = some true → evaluateFormula values conclusion = some true := by
  have zero := points_zero_iff_named names (counterexamples premise conclusion) result success
  obtain ⟨compiled, parsed, _, _, _⟩ := points_success names (counterexamples premise conclusion) result success
  have defined : ∀ values : Name → Int, ∃ value, evaluateFormula values (counterexamples premise conclusion) = some value := by
    intro values
    obtain ⟨value, evaluated, _⟩ := signed_indicator (variableOf names) values (coordinateValues names values)
      (coordinateValues_correct names values) (counterexamples premise conclusion) compiled parsed
    exact ⟨value, evaluated⟩
  simp only [implication, success]
  have verdict : (if result.count = 0 then Verdict.yes else Verdict.no) = .yes ↔ result.count = 0 := by
    by_cases empty : result.count = 0 <;> simp [empty]
  rw [verdict, zero]
  exact forall_congr' (fun values => counterexamples_false_iff values premise conclusion (defined values))

/-- A definite yes is sound even when unsupported cases can return unknown. -/
theorem implication_yes [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (yes : implication names premise conclusion = .yes) :
    ∀ values : Name → Int, evaluateFormula values premise = some true → evaluateFormula values conclusion = some true := by
  cases counted : points names (counterexamples premise conclusion) with
  | error error => simp [implication, counted] at yes
  | ok result => exact (implication_named_iff names premise conclusion result counted).mp yes

/-- A definite no has a genuine counterexample among named integer valuations. -/
theorem implication_no [DecidableEq Name] (names : List Name) (premise conclusion : Formula Name)
    (no : implication names premise conclusion = .no) :
    ∃ values : Name → Int, evaluateFormula values premise = some true ∧ evaluateFormula values conclusion ≠ some true := by
  classical
  cases counted : points names (counterexamples premise conclusion) with
  | error error => simp [implication, counted] at no
  | ok result =>
    have notValid : ¬∀ values : Name → Int,
        evaluateFormula values premise = some true → evaluateFormula values conclusion = some true := by
      intro valid
      have yes := (implication_named_iff names premise conclusion result counted).mpr valid
      rw [no] at yes
      cases yes
    obtain ⟨values, bad⟩ := Classical.not_forall.mp notValid
    by_cases premiseTrue : evaluateFormula values premise = some true
    · exact ⟨values, premiseTrue, fun conclusionTrue => bad (fun _ => conclusionTrue)⟩
    · exact False.elim (bad (fun accepted => False.elim (premiseTrue accepted)))

end MicroCFTA.LatticeAPI
