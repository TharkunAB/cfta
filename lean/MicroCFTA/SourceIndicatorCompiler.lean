import MicroCFTA.SourceEqualityGuards

/-!
# The full source guard-to-indicator adapter

The compiler reads every Boolean operand in list order. Theory guards and
substitutions return the complete unsupported operand as the error payload.
Compilation does not use the truth of another operand or stored equalities.
-/
namespace MicroCFTA.SourceIndicatorCompiler
open SourceGuards SourceEqualityGuards
open ConstraintIndicators (Series conjoin complement)

mutual
/-- The complete source dispatch, including the exact unsupported guard payload. -/
def guardTerms : Guard Formula → Except (Guard Formula) (Series (List Path))
  | .top => .ok [(1, [])]
  | .bottom => .ok []
  | .same left right => .ok [(1, [[left, right]])]
  | .not inner => (guardTerms inner).map complement
  | .and parts => (guardList parts).map (fun rows => rows.foldl conjoin [(1, [])])
  | .or parts => (guardList parts).map (fun rows => complement ((rows.map complement).foldl conjoin [(1, [])]))
  | guard => .error guard

/-- Traverse every Boolean operand from left to right and retain the first error. -/
def guardList : List (Guard Formula) → Except (Guard Formula) (List (Series (List Path)))
  | [] => .ok []
  | first :: rest => do
      let row ← guardTerms first
      let rows ← guardList rest
      pure (row :: rows)
end

/-- Stored equalities multiply the successful guard rows after guard compilation. -/
def constraintIndicators (equalities : Option (List (List Path))) (guard : Guard Formula) :
    Except (Guard Formula) (Series (List Path)) :=
  (guardTerms guard).map (conjoin (ConstraintIndicators.equalityIndicators equalities))

/-- Converting path pairs to raw equality classes commutes with source complement. -/
theorem classes_complement (rows : Series (Path × Path)) :
    classes (complement rows) = complement (classes rows) := by
  simp [classes, complement, List.map_map, Function.comp_def]

/-- Converting path pairs preserves the exact Cartesian row order and repetitions. -/
theorem classes_conjoin (left right : Series (Path × Path)) :
    classes (conjoin left right) = conjoin (classes left) (classes right) := by
  simp [classes, conjoin, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, List.map_append]

/-- Conversion preserves the source left fold, including its initial row. -/
theorem classes_fold (rows : List (Series (Path × Path))) (initial : Series (Path × Path)) :
    classes (rows.foldl conjoin initial) = (rows.map classes).foldl conjoin (classes initial) := by
  induction rows generalizing initial with
  | nil => rfl
  | cons first rest ih => simp only [List.foldl_cons, ih, List.map_cons, classes_conjoin]

/-- A successful full-source compilation contains only the supported Boolean syntax,
and its output is exactly the generic compiler's raw equality-class series. -/
theorem successful_fragment (guard : Guard Formula) (result : Series (List Path))
    (success : guardTerms guard = .ok result) :
    ∃ boolean pairs, source boolean = guard ∧ ConstraintIndicators.compile boolean = .ok pairs ∧
      classes pairs = result := by
  induction guard using Guard.rec
    (motive_2 := fun guards => ∀ parts, guardList guards = .ok parts →
      ∃ booleans pairs, sources booleans = guards ∧ ConstraintIndicators.compileList booleans = .ok pairs ∧
        pairs.map classes = parts)
    generalizing result with
  | top => cases success; exact ⟨.top, [(1, [])], rfl, rfl, rfl⟩
  | bottom => cases success; exact ⟨.bottom, [], rfl, rfl, rfl⟩
  | same left right => cases success; exact ⟨.same (left, right), [(1, [(left, right)])], rfl, rfl, rfl⟩
  | entails | satisfies | holds | substitute => cases success
  | not inner ih =>
      cases compiled : guardTerms inner with
      | error error => simp [guardTerms, compiled, Except.map] at success
      | ok rows =>
          obtain ⟨boolean, pairs, shape, compile, exactRows⟩ := ih rows compiled
          have same : complement rows = result := by simpa [guardTerms, compiled, Except.map] using success
          refine ⟨.not boolean, complement pairs, ?_, ?_, ?_⟩
          · simp only [source, shape]
          · simp only [ConstraintIndicators.compile, compile, Except.map]
          · rw [classes_complement, exactRows, same]
  | and parts ih =>
      cases compiled : guardList parts with
      | error error => simp [guardTerms, compiled, Except.map] at success
      | ok rows =>
          obtain ⟨booleans, pairs, shape, compile, exactRows⟩ := ih rows compiled
          have same : rows.foldl conjoin [(1, [])] = result := by simpa [guardTerms, compiled, Except.map] using success
          refine ⟨.and booleans, pairs.foldl conjoin [(1, [])], ?_, ?_, ?_⟩
          · simp only [source, shape]
          · simp only [ConstraintIndicators.compile, compile, Except.map]
          · rw [classes_fold, exactRows]; exact same
  | or parts ih =>
      cases compiled : guardList parts with
      | error error => simp [guardTerms, compiled, Except.map] at success
      | ok rows =>
          obtain ⟨booleans, pairs, shape, compile, exactRows⟩ := ih rows compiled
          have same : complement ((rows.map complement).foldl conjoin [(1, [])]) = result :=
            by simpa [guardTerms, compiled, Except.map] using success
          refine ⟨.or booleans, complement ((pairs.map complement).foldl conjoin [(1, [])]), ?_, ?_, ?_⟩
          · simp only [source, shape]
          · simp only [ConstraintIndicators.compile, compile, Except.map]
          · rw [classes_complement, classes_fold]
            have mapped : (pairs.map complement).map classes = rows.map complement := by
              rw [List.map_map, ← exactRows, List.map_map]
              exact List.map_congr_left (fun _ _ => classes_complement _)
            rw [mapped]; exact same
  | nil =>
      rename_i parts success
      cases success
      exact ⟨[], [], rfl, rfl, rfl⟩
  | cons first rest ih ir =>
      rename_i parts success
      cases head : guardTerms first with
      | error error => simp [guardList, head, Bind.bind, Except.bind] at success
      | ok row =>
          cases tail : guardList rest with
          | error error => simp [guardList, head, tail, Bind.bind, Except.bind] at success
          | ok rows =>
              obtain ⟨boolean, pair, shape, compile, exactRow⟩ := ih row head
              obtain ⟨booleans, pairs, shapes, compiles, exactRows⟩ := ir rows tail
              have same : row :: rows = parts := by
                simpa [guardList, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using success
              refine ⟨boolean :: booleans, pair :: pairs, ?_, ?_, ?_⟩
              · simp only [sources, shape, shapes]
              · simp [ConstraintIndicators.compileList, compile, compiles, Bind.bind, Except.bind,
                  Pure.pure, Except.pure]
              · simp only [List.map_cons, exactRow, exactRows, same]

/-- The full adapter reproduces the generic compiler's exact rows on supported syntax. -/
theorem source_compile (boolean : BooleanGuard) (pairs : Series (Path × Path))
    (compiled : ConstraintIndicators.compile boolean = .ok pairs) :
    guardTerms (source (Formula := Formula) boolean) = .ok (classes pairs) := by
  induction boolean using ConstraintIndicators.Guard.rec
    (motive_2 := fun booleans => ∀ parts, ConstraintIndicators.compileList booleans = .ok parts →
      guardList (sources (Formula := Formula) booleans) = .ok (parts.map classes))
    generalizing pairs with
  | top | bottom | same => cases compiled; rfl
  | residual impossible => cases impossible
  | not inner ih =>
      obtain ⟨rows, result⟩ := compile_total inner
      have same : complement rows = pairs := by simpa [ConstraintIndicators.compile, result, Except.map] using compiled
      rw [← same, classes_complement]
      simp only [source, guardTerms, ih rows result, Except.map]
  | and parts ih =>
      cases result : ConstraintIndicators.compileList parts with
      | error impossible => cases impossible
      | ok rows =>
          have same : rows.foldl conjoin [(1, [])] = pairs :=
            by simpa [ConstraintIndicators.compile, result, Except.map] using compiled
          rw [← same, classes_fold]
          simp only [source, guardTerms, ih rows result, Except.map]
          rfl
  | or parts ih =>
      cases result : ConstraintIndicators.compileList parts with
      | error impossible => cases impossible
      | ok rows =>
          have same : complement ((rows.map complement).foldl conjoin [(1, [])]) = pairs :=
            by simpa [ConstraintIndicators.compile, result, Except.map] using compiled
          rw [← same, classes_complement, classes_fold]
          simp only [source, guardTerms, ih rows result, Except.map]
          have mapped : (rows.map complement).map classes = (rows.map classes).map complement := by
            simp only [List.map_map]
            exact List.map_congr_left (fun _ _ => classes_complement _)
          rw [mapped]; rfl
  | nil => rename_i parts compiled; cases compiled; rfl
  | cons first rest ih ir =>
      rename_i parts compiled
      obtain ⟨row, head⟩ := compile_total first
      cases tail : ConstraintIndicators.compileList rest with
      | error impossible => cases impossible
      | ok rows =>
          have same : row :: rows = parts := by
            simpa [ConstraintIndicators.compileList, head, tail, Bind.bind, Except.bind,
              Pure.pure, Except.pure] using compiled
          rw [← same]
          simp [sources, guardList, ih row head, ir rows tail, Bind.bind, Except.bind,
            Pure.pure, Except.pure]

/-- Successful source compilation is equivalent to membership in the supported fragment. -/
theorem successful_iff_supported (guard : Guard Formula) :
    (∃ rows, guardTerms guard = .ok rows) ↔ ∃ boolean, source boolean = guard := by
  constructor
  · rintro ⟨rows, compiled⟩
    obtain ⟨boolean, _, shape, _, _⟩ := successful_fragment guard rows compiled
    exact ⟨boolean, shape⟩
  · rintro ⟨boolean, shape⟩
    obtain ⟨pairs, compiled⟩ := compile_total boolean
    rw [← shape]
    exact ⟨classes pairs, source_compile boolean pairs compiled⟩

/-- Source substitution is opaque to this compiler, including an empty substitution list. -/
theorem substitute_error (additions : List Substitution) (inner : Guard Formula) :
    guardTerms (.substitute additions inner) = .error (.substitute additions inner) := rfl

/-- Negation does not change the unsupported payload found in its operand. -/
theorem not_error (guard bad : Guard Formula) (failed : guardTerms guard = .error bad) :
    guardTerms (.not guard) = .error bad := by simp [guardTerms, failed, Except.map]

/-- A successful prefix cannot hide the first error or let the suffix replace it. -/
theorem first_error (initial : List (Guard Formula)) (rows : List (Series (List Path)))
    (prefixSuccess : guardList initial = .ok rows) (guard bad : Guard Formula)
    (failed : guardTerms guard = .error bad) (rest : List (Guard Formula)) :
    guardList (initial ++ guard :: rest) = .error bad := by
  induction initial generalizing rows with
  | nil => simp [guardList, failed, Bind.bind, Except.bind]
  | cons first tail ih =>
      cases head : guardTerms first with
      | error error => simp [guardList, head, Bind.bind, Except.bind] at prefixSuccess
      | ok row =>
          cases remaining : guardList tail with
          | error error => simp [guardList, head, remaining, Bind.bind, Except.bind] at prefixSuccess
          | ok remainingRows =>
              simp [guardList, head, ih remainingRows remaining, Bind.bind, Except.bind]

/-- Both Boolean list constructors preserve the same first unsupported operand. -/
theorem boolean_first_error (initial : List (Guard Formula)) (rows : List (Series (List Path)))
    (prefixSuccess : guardList initial = .ok rows) (guard bad : Guard Formula)
    (failed : guardTerms guard = .error bad) (rest : List (Guard Formula)) :
    guardTerms (.and (initial ++ guard :: rest)) = .error bad ∧
      guardTerms (.or (initial ++ guard :: rest)) = .error bad := by
  simp [guardTerms, first_error initial rows prefixSuccess guard bad failed rest, Except.map]

/-- Even contradictory stored equalities retain the exact unsupported operand. -/
theorem constraint_error (equalities : Option (List (List Path))) (guard bad : Guard Formula)
    (failed : guardTerms guard = .error bad) :
    constraintIndicators equalities guard = .error bad := by
  simp [constraintIndicators, failed, Except.map]

/-- False conjunctions still reject their first unsupported operand. -/
theorem false_and_theory (first second : Path) (later : Guard Formula) :
    guardTerms (.and [.bottom, .entails first second, later]) = .error (.entails first second) := rfl

/-- True disjunctions still reject their first unsupported operand. -/
theorem true_or_substitute (inner later : Guard Formula) :
    guardTerms (.or [.top, .substitute [] inner, later]) = .error (.substitute [] inner) := rfl

/-- A contradictory stored equality set does not suppress a theory error under negation. -/
theorem false_equalities_theory (targets : List Path) (formula : Formula) :
    constraintIndicators none (.not (.holds targets formula)) = .error (.holds targets formula) := rfl

/-- Error payloads retain the entire substitution, without inspecting its unsupported body. -/
theorem opaque_substitute_error (target : Path) (formula : Formula) :
    guardTerms (.substitute [] (.satisfies target formula)) =
      .error (.substitute [] (.satisfies target formula)) := rfl

/-- Stored equalities retain the exact successfully compiled fragment and row product. -/
theorem successful_constraint_fragment (equalities : Option (List (List Path)))
    (guard : Guard Formula) (rows : Series (List Path))
    (success : constraintIndicators equalities guard = .ok rows) :
    ∃ boolean pairs, source boolean = guard ∧ ConstraintIndicators.compile boolean = .ok pairs ∧
      conjoin (ConstraintIndicators.equalityIndicators equalities) (classes pairs) = rows := by
  cases compiled : guardTerms guard with
  | error error => simp [constraintIndicators, compiled, Except.map] at success
  | ok parts =>
      obtain ⟨boolean, pairs, shape, generic, exactRows⟩ := successful_fragment guard parts compiled
      refine ⟨boolean, pairs, shape, generic, ?_⟩
      rw [exactRows]
      simpa [constraintIndicators, compiled, Except.map] using success

/-- The equality component does not alter which source guards the compiler supports. -/
theorem constraint_successful_iff_supported (equalities : Option (List (List Path)))
    (guard : Guard Formula) :
    (∃ rows, constraintIndicators equalities guard = .ok rows) ↔ ∃ boolean, source boolean = guard := by
  constructor
  · rintro ⟨rows, compiled⟩
    obtain ⟨boolean, _, shape, _, _⟩ := successful_constraint_fragment equalities guard rows compiled
    exact ⟨boolean, shape⟩
  · intro supported
    obtain ⟨rows, compiled⟩ := (successful_iff_supported guard).mpr supported
    exact ⟨conjoin (ConstraintIndicators.equalityIndicators equalities) rows,
      by simp [constraintIndicators, compiled, Except.map]⟩

/-- Every actual successful full-source guard compilation has the exact public guard score. -/
theorem successful_guard_score [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (term : Language.Term (SourceObservations.Label Formula))
    (guard : Guard Formula) (rows : Series (List Path)) (success : guardTerms guard = .ok rows) :
    ConstraintIndicators.score (SymbolicDriver.classTest term) rows = Lattice.indicator
      (decide (SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes)) := by
  obtain ⟨boolean, pairs, shape, compiled, exactRows⟩ := successful_fragment guard rows success
  rw [← shape, ← exactRows]
  exact compiled_classes_exact formulas solver term boolean pairs compiled

/-- The concrete source adapter supplies the guard-score premise of the total symbolic index API. -/
theorem successful_constraint_score [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (term : Language.Term (SourceObservations.Label Formula))
    (equalities : Option (List (List Path))) (guard : Guard Formula) (rows : Series (List Path))
    (success : constraintIndicators equalities guard = .ok rows) :
    ConstraintIndicators.score (SymbolicDriver.classTest term) rows = Lattice.indicator
      (ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) equalities &&
        decide (SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes)) := by
  cases compiled : guardTerms guard with
  | error error => simp [constraintIndicators, compiled, Except.map] at success
  | ok parts =>
      have same : conjoin (ConstraintIndicators.equalityIndicators equalities) parts = rows := by
        simpa [constraintIndicators, compiled, Except.map] using success
      rw [← same, ConstraintIndicators.score_conjoin, ConstraintIndicators.equality_correct,
        successful_guard_score formulas solver term guard parts compiled, Lattice.indicator_and]

end MicroCFTA.SourceIndicatorCompiler
