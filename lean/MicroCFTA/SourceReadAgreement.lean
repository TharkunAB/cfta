import MicroCFTA.SourceGuardRefinement

/-!
# Guard evaluation depends on its planned reads

Refinement-only positions can have different constructor names. Structural
comparisons and actual/formal positions require the full root observation.
This module proves that dependency for the complete source guard control.
-/
namespace MicroCFTA.SourceReadAgreement
open SourceGuards SourceObservations

/-- The two kinds of source read agree at the positions requested by a guard. -/
structure Reads (guard : Guard Formula) (first second : Observations Formula) : Prop where
  refinements : ∀ path ∈ paths guard, (first path).map Observed.refinement = (second path).map Observed.refinement
  symbols : ∀ path ∈ sensitive guard, first path = second path

/-- A nested guard retains the required part of its enclosing read agreement. -/
theorem restrict (outer inner : Guard Formula) (first second : Observations Formula)
    (reads : Reads outer first second)
    (allPaths : ∀ path ∈ paths inner, path ∈ paths outer)
    (allSensitive : ∀ path ∈ sensitive inner, path ∈ sensitive outer) : Reads inner first second :=
  ⟨fun path member => reads.refinements path (allPaths path member),
   fun path member => reads.symbols path (allSensitive path member)⟩

/-- Reading all target refinements ignores the observed constructor names and shape. -/
theorem observeMany_refinements (first second : Observations Formula) (targets : List Path)
    (agree : ∀ target ∈ targets, (first target).map Observed.refinement = (second target).map Observed.refinement) :
    (observeMany first targets).map (List.map Observed.refinement) =
      (observeMany second targets).map (List.map Observed.refinement) := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      have head := agree target (by simp)
      have tail := ih (fun path member => agree path (by simp [member]))
      cases a : first target <;> cases b : second target <;>
        cases c : observeMany first rest <;> cases d : observeMany second rest <;>
        simp_all [observeMany]

private theorem contract_zip_congr (formulas : Formulas Formula) (formals : List Name)
    (first second : List (Observed Formula))
    (same : first.map Observed.refinement = second.map Observed.refinement) :
    ((formals.zip first).map fun (formal, value) => formulas.substitute [(valueName, formal)] value.refinement) =
      ((formals.zip second).map fun (formal, value) => formulas.substitute [(valueName, formal)] value.refinement) := by
  induction formals generalizing first second with
  | nil => rfl
  | cons formal rest ih =>
      cases first <;> cases second <;> simp_all
      exact ih _ _ same.2

/-- A Holds query uses exactly the target refinement list and its fixed repeated-path aliases. -/
theorem contract_refinements (formulas : Formulas Formula) (targets : List Path)
    (first second : List (Observed Formula))
    (same : first.map Observed.refinement = second.map Observed.refinement) :
    contract formulas targets first = contract formulas targets second := by
  unfold contract
  dsimp only
  rw [contract_zip_congr formulas _ first second same]

/-- Resolving a scope uses only the two full observations of each source substitution. -/
theorem resolveMany_reads (formulas : Formulas Formula) (first second : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (additions : List Substitution)
    (agree : ∀ entry ∈ additions, first entry.actual = second entry.actual ∧ first entry.formal = second entry.formal) :
    resolveMany formulas first fresh unknown additions = resolveMany formulas second fresh unknown additions := by
  induction additions with
  | nil => rfl
  | cons entry rest ih =>
      have head := agree entry (by simp)
      have tail := ih (fun other member => agree other (by simp [member]))
      simp only [resolveMany, resolve, head.1, head.2, tail]

/-- Every source guard computation depends only on the planned reads and its supplied actual tables. -/
theorem evaluate_reads [DecidableEq Formula] (formulas : Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (first second : Observations Formula) (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : Guard Formula)
    (reads : Reads guard first second) :
    evaluateWith formulas solver first (sameShape formulas first) fresh unknown scopes positive guard =
      evaluateWith formulas solver second (sameShape formulas second) fresh unknown scopes positive guard := by
  cases guard with
  | top | bottom => simp only [evaluateWith]
  | same left right =>
      have hl := reads.symbols left (by simp [sensitive])
      have hr := reads.symbols right (by simp [sensitive])
      simp only [evaluateWith, sameShape, hl, hr]
  | entails left right =>
      have hl := reads.refinements left (by simp [paths])
      have hr := reads.refinements right (by simp [paths])
      cases a : first left <;> cases b : second left <;> cases c : first right <;> cases d : second right <;>
        simp_all [evaluateWith]
  | satisfies target requirement =>
      have ht := reads.refinements target (by simp [paths])
      cases a : first target <;> cases b : second target <;> simp_all [evaluateWith]
  | holds targets requirement =>
      have observed := observeMany_refinements first second targets (by simpa [paths] using reads.refinements)
      cases a : observeMany first targets <;> cases b : observeMany second targets <;>
        simp only [a, b, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at observed
      all_goals try contradiction
      · simp only [evaluateWith, a, b]
      · simp only [evaluateWith, a, b]
        rw [contract_refinements formulas targets _ _ observed]
  | substitute additions inner =>
      have resolutions := resolveMany_reads formulas first second fresh unknown additions (fun entry member =>
        ⟨reads.symbols entry.actual (by simp [sensitive, List.mem_flatMap]; exact Or.inl ⟨entry, member, Or.inl rfl⟩),
         reads.symbols entry.formal (by simp [sensitive, List.mem_flatMap]; exact Or.inl ⟨entry, member, Or.inr rfl⟩)⟩)
      have nested := restrict _ inner first second reads
        (fun path member => by simp [paths, member])
        (fun path member => by simp [sensitive, member])
      simp only [evaluateWith, resolutions]
      cases resolved : resolveMany formulas second fresh unknown additions with
      | none => rfl
      | some scope => exact evaluate_reads formulas solver first second fresh unknown (scope :: scopes) positive inner nested
  | not inner =>
      have nested : Reads inner first second :=
        ⟨by simpa [paths] using reads.refinements, by simpa [sensitive] using reads.symbols⟩
      simp only [evaluateWith]
      exact evaluate_reads formulas solver first second fresh unknown scopes (!positive) inner nested
  | and parts | or parts =>
      simp only [evaluateWith]
      congr 1
      apply List.map_congr_left
      intro part member
      apply evaluate_reads formulas solver first second fresh unknown scopes positive part
      exact restrict _ part first second reads
        (fun path present => by simp [paths, List.mem_flatMap]; exact ⟨part, member, present⟩)
        (fun path present => by simp [sensitive, List.mem_flatMap]; exact ⟨part, member, present⟩)
termination_by sizeOf guard

/-- Every full-symbol request is also an ordinary requested guard path. -/
theorem sensitive_requested (guard : Guard Formula) (path : Path) (member : path ∈ sensitive guard) :
    path ∈ paths guard := by
  cases guard with
  | top | bottom | entails _ _ | satisfies _ _ | holds _ _ => simp [sensitive] at member
  | same _ _ => simpa [sensitive, paths] using member
  | substitute additions inner =>
      simp only [paths]
      simp only [sensitive, List.mem_append] at member
      rcases member with outer | nested
      · exact List.mem_append_left _ outer
      · exact List.mem_append_right _ (sensitive_requested inner path nested)
  | not inner =>
      simp only [sensitive] at member
      simpa only [paths] using sensitive_requested inner path member
  | and parts | or parts =>
      simp only [sensitive] at member
      simp only [paths]
      obtain ⟨part, present, nested⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨part, present, sensitive_requested part path nested⟩
termination_by sizeOf guard

/-- The source partition retains either an annotation or a complete symbol and shape. -/
inductive SignatureEntry (Formula : Type) where
  | refinement (formula : Formula)
  | symbol (observed : Observed Formula)

/-- A path-indexed view of the source guard signature has no unrequested entries. -/
def signature (guard : Guard Formula) (observed : Observations Formula) (path : Path) : Option (SignatureEntry Formula) :=
  if path ∈ paths guard then
    (observed path).map (fun value => if path ∈ sensitive guard then .symbol value else .refinement value.refinement)
  else none

/-- Equal source signature entries provide exactly the evaluator's required read agreement. -/
theorem signature_reads (guard : Guard Formula) (first second : Observations Formula)
    (equal : signature guard first = signature guard second) : Reads guard first second := by
  constructor
  · intro path requested
    have entry := congrFun equal path
    simp only [signature, requested, ↓reduceIte] at entry
    by_cases full : path ∈ sensitive guard <;>
      cases a : first path <;> cases b : second path <;> simp_all
  · intro path full
    have entry := congrFun equal path
    have requested := sensitive_requested guard path full
    simp only [signature, requested, full, ↓reduceIte] at entry
    cases a : first path <;> cases b : second path <;> simp_all

/-- A guard without actual positions needs no declaration or ambiguity table. -/
theorem no_actual_tables [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) (none : actualPaths guard = []) :
    substitutionValues formulas observed sameAt guard = ([], []) := by
  simp [substitutionValues, actuals, none, orderedPaths, allocated, conflicts, values, ambiguous]

/-- Without actual substitutions, equal source signatures give identical full guard decisions. -/
theorem signature_evaluator_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (guard : Guard Formula) (first second : Observations Formula)
    (noActual : actualPaths guard = []) (equal : signature guard first = signature guard second) :
    evaluateGuardWithShape formulas solver first guard = evaluateGuardWithShape formulas solver second guard := by
  unfold evaluateGuardWithShape evaluateGuardWithSame
  rw [no_actual_tables formulas first _ guard noActual, no_actual_tables formulas second _ guard noActual]
  exact evaluate_reads formulas solver first second [] [] [] true guard (signature_reads guard first second equal)

end MicroCFTA.SourceReadAgreement
