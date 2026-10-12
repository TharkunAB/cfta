import MicroCFTA.SourceBooleanEntry
import MicroCFTA.SymbolicIndicators

/-!
# Equality indicators and the current public guard evaluator

The supported Boolean fragment uses only Top, Bottom, Same, Not, And, and
Or. Same requires both paths to exist, including a reflexive path pair.
-/
namespace MicroCFTA.SourceEqualityGuards
open SourceGuards SourceObservations Language

/-- The complete source fragment accepted by the solver-free indicator compiler. -/
abbrev BooleanGuard := ConstraintIndicators.Guard (Path × Path) Empty

mutual
/-- Retain the actual source Boolean constructors and both ordered equality paths. -/
def source : BooleanGuard → Guard Formula
  | .top => .top
  | .bottom => .bottom
  | .same pair => .same pair.1 pair.2
  | .not inner => .not (source inner)
  | .and parts => .and (sources parts)
  | .or parts => .or (sources parts)
  | .residual impossible => nomatch impossible

/-- Source Boolean list order and repetitions remain unchanged. -/
def sources : List BooleanGuard → List (Guard Formula)
  | [] => []
  | first :: rest => source first :: sources rest
end

/-- Independent equality checks both path lookups before structural equality. -/
def pairTest [DecidableEq Formula] (term : Term (Label Formula)) (pair : Path × Path) : Bool :=
  match term.atPath pair.1, term.atPath pair.2 with
  | some left, some right => termEq left right
  | _, _ => false

/-- Equality-only guards never need an Unknown atomic answer. -/
def verdict (value : Bool) : Guards.Verdict := if value then .yes else .no

/-- Reading a guard under pushed source polarity. -/
def signed (positive value : Bool) : Guards.Verdict := polarize positive (verdict value)

private theorem rename_empty (formulas : Formulas Formula) (term : Term (Label Formula)) :
    renameTree formulas [] term = term := by
  induction term using Term.rec
    (motive_2 := fun terms => terms.map (renameTree formulas []) = terms) with
  | node label children ih => simp only [renameTree, renameRoot, List.foldl_nil, ih]
  | nil => rfl
  | cons first rest ih ir => simp [ih, ir]

/-- Current complete Same is exact structural equality with required path existence. -/
theorem same_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (positive : Bool) (left right : Path) :
    SourceBooleanEntry.evaluate formulas solver (observe term) (sameTerm formulas term) positive (.same left right) =
      signed positive (pairTest term (left, right)) := by
  simp only [SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, evaluateWith, observe,
    sameTerm, pairTest]
  cases l : term.atPath left <;> cases r : term.atPath right <;>
    simp only [Option.map_none, Option.map_some, rename_empty]
  all_goals try (cases positive <;> rfl)
  rename_i first second
  by_cases equalPaths : left = right
  · subst right
    have same : first = second := by simpa [l] using r
    subst second
    have reflexive := (termEq_correct first first).mpr rfl
    simp [signed, verdict, reflexive]
  · simp only [equalPaths, ↓reduceIte]
    cases answer : termEq first second <;> simp [answer, signed, verdict]

private theorem combine_signed (positive : Bool) (values : List Bool) :
    combine positive (values.map (signed positive)) = signed positive (values.all id) := by
  induction values with
  | nil => cases positive <;> rfl
  | cons first rest ih =>
      simp only [List.map_cons, GuardConjunction.combine_cons, ih, List.all_cons]
      cases positive <;> cases first <;> cases rest.all id <;> rfl

private theorem disjoin_signed (positive : Bool) (values : List Bool) :
    combine (!positive) (values.map (signed positive)) = signed positive (values.any id) := by
  induction values with
  | nil => cases positive <;> rfl
  | cons first rest ih =>
      simp only [List.map_cons, GuardConjunction.combine_cons, ih, List.any_cons]
      cases positive <;> cases first <;> cases rest.any id <;> rfl

mutual
/-- Every supported source guard has exactly the compiled Boolean meaning in both polarities. -/
theorem evaluate_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (positive : Bool) (guard : BooleanGuard) :
    SourceBooleanEntry.evaluate formulas solver (observe term) (sameTerm formulas term) positive (source guard) =
      signed positive (ConstraintIndicators.eval (pairTest term) Empty.elim guard) := by
  cases guard with
  | top | bottom => cases positive <;>
      simp [source, SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, evaluateWith,
        ConstraintIndicators.eval, signed, verdict, polarize, Guards.negate]
  | same pair => exact same_exact formulas solver term positive pair.1 pair.2
  | not inner =>
      simp only [source, SourceBooleanEntry.evaluate, evaluate_exact formulas solver term (!positive) inner,
        ConstraintIndicators.eval]
      cases positive <;> cases ConstraintIndicators.eval (pairTest term) Empty.elim inner <;> rfl
  | and parts =>
      simp only [source, SourceBooleanEntry.evaluate, list_exact, combine_signed, ConstraintIndicators.eval]
      rw [eval_all]
  | or parts =>
      simp only [source, SourceBooleanEntry.evaluate, list_exact, disjoin_signed, ConstraintIndicators.eval]
      rw [eval_any]
  | residual impossible => cases impossible

/-- The concrete source list entry evaluates every Boolean part in order. -/
theorem list_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (positive : Bool) (parts : List BooleanGuard) :
    (sources parts).map (SourceBooleanEntry.evaluate formulas solver (observe term) (sameTerm formulas term) positive) =
      (parts.map (ConstraintIndicators.eval (pairTest term) Empty.elim)).map (signed positive) := by
  cases parts with
  | nil => rfl
  | cons first rest => simp only [sources, List.map_cons, evaluate_exact, list_exact]

/-- The compiled list conjunction is the ordinary Boolean all fold. -/
theorem eval_all (test : (Path × Path) → Bool) (parts : List BooleanGuard) :
    (parts.map (ConstraintIndicators.eval test Empty.elim)).all id = ConstraintIndicators.all test Empty.elim parts := by
  cases parts with
  | nil => rfl
  | cons first rest => simp only [List.map_cons, List.all_cons, ConstraintIndicators.all, eval_all, id_eq]

/-- The compiled list disjunction is the ordinary Boolean any fold. -/
theorem eval_any (test : (Path × Path) → Bool) (parts : List BooleanGuard) :
    (parts.map (ConstraintIndicators.eval test Empty.elim)).any id = ConstraintIndicators.any test Empty.elim parts := by
  cases parts with
  | nil => rfl
  | cons first rest => simp only [List.map_cons, List.any_cons, ConstraintIndicators.any, eval_any, id_eq]
end

/-- Successful signed compilation has the exact current complete guard indicator. -/
theorem compiled_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (guard : BooleanGuard) (series : ConstraintIndicators.Series (Path × Path))
    (compiled : ConstraintIndicators.compile guard = .ok series) :
    ConstraintIndicators.score (pairTest term) series = Lattice.indicator
      (decide (SourceBooleanEntry.evaluateGuard formulas solver (source guard) term = .yes)) := by
  rw [ConstraintIndicators.compile_correct (pairTest term) Empty.elim guard series compiled]
  unfold SourceBooleanEntry.evaluateGuard SourceBooleanEntry.evaluateGuardWithSame
  rw [evaluate_exact]
  cases ConstraintIndicators.eval (pairTest term) Empty.elim guard <;> rfl

/-- The symbolic path class has the same existence-sensitive meaning as current Same. -/
theorem pair_class [DecidableEq Formula] (term : Term (Label Formula)) (pair : Path × Path) :
    SymbolicDriver.classTest term [pair.1, pair.2] = pairTest term pair := by
  apply Bool.eq_iff_iff.mpr
  simp only [SymbolicDriver.classTest, decide_eq_true_eq]
  simp only [Symbolic.ClassSatisfied, List.mem_singleton, forall_eq, pairTest]
  cases leftFound : term.atPath pair.1 <;> cases rightFound : term.atPath pair.2 <;>
    simp_all [termEq_correct]
  exact eq_comm

/-- The source writes each Same pair as one two-path equality class. -/
def classes (series : ConstraintIndicators.Series (Path × Path)) : ConstraintIndicators.Series (List Path) :=
  series.map (fun entry => (entry.1, entry.2.map (fun pair => [pair.1, pair.2])))

/-- Turning source path pairs into the exact raw classes preserves the signed score. -/
theorem classes_score [DecidableEq Formula] (term : Term (Label Formula))
    (series : ConstraintIndicators.Series (Path × Path)) :
    ConstraintIndicators.score (SymbolicDriver.classTest term) (classes series) =
      ConstraintIndicators.score (pairTest term) series := by
  unfold classes ConstraintIndicators.score
  simp only [List.map_map, List.all_map, Function.comp_def, pair_class]

/-- The exact raw symbolic guard rows describe precisely the current public confirmed language. -/
theorem compiled_classes_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (guard : BooleanGuard) (series : ConstraintIndicators.Series (Path × Path))
    (compiled : ConstraintIndicators.compile guard = .ok series) :
    ConstraintIndicators.score (SymbolicDriver.classTest term) (classes series) = Lattice.indicator
      (decide (SourceBooleanEntry.evaluateGuard formulas solver (source guard) term = .yes)) := by
  rw [classes_score]
  exact compiled_exact formulas solver term guard series compiled

/-- Stored normalized equalities and compiled Boolean guards supply the symbolic edge-score premise. -/
theorem constraint_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Term (Label Formula)) (equalities : Option (List (List Path))) (guard : BooleanGuard)
    (series : ConstraintIndicators.Series (Path × Path))
    (compiled : ConstraintIndicators.compile guard = .ok series) :
    ConstraintIndicators.score (SymbolicDriver.classTest term)
      (ConstraintIndicators.conjoin (ConstraintIndicators.equalityIndicators equalities) (classes series)) =
      Lattice.indicator (ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) equalities &&
        decide (SourceBooleanEntry.evaluateGuard formulas solver (source guard) term = .yes)) := by
  rw [ConstraintIndicators.score_conjoin, ConstraintIndicators.equality_correct,
    compiled_classes_exact formulas solver term guard series compiled, Lattice.indicator_and]

/-- Every guard in the actual supported fragment compiles; it has no residual error case. -/
theorem compile_total (guard : BooleanGuard) :
    ∃ series, ConstraintIndicators.compile guard = .ok series := by
  cases result : ConstraintIndicators.compile guard with
  | error impossible => cases impossible
  | ok series => exact ⟨series, rfl⟩

/-- The source Boolean fragment supplies exact signed rows for every complete term. -/
theorem constraint_rows [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (equalities : Option (List (List Path))) (guard : BooleanGuard) :
    ∃ series, ConstraintIndicators.compile guard = .ok series ∧
      ∀ term : Term (Label Formula),
        ConstraintIndicators.score (SymbolicDriver.classTest term)
          (ConstraintIndicators.conjoin (ConstraintIndicators.equalityIndicators equalities) (classes series)) =
        Lattice.indicator (ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) equalities &&
          decide (SourceBooleanEntry.evaluateGuard formulas solver (source guard) term = .yes)) := by
  obtain ⟨series, compiled⟩ := compile_total guard
  exact ⟨series, compiled, fun term => constraint_exact formulas solver term equalities guard series compiled⟩

end MicroCFTA.SourceEqualityGuards
