import MicroCFTA.SourceGuards

/-!
# Sparse structural comparisons under source name substitution

Root observations can decide unequal symbols, equal leaves, and leaf/inner
mismatches. They leave equal-root inner terms Unknown. The proofs connect each
decided sparse result to the actual renamed complete-tree comparison.
-/
namespace MicroCFTA.SourceObservations
open SourceGuards

/-- Constructor names and complete refinement annotations form the structural alphabet. -/
abbrev Label (Formula : Type) := Name × Formula

/-- The source first non-identity mapping wins for each repeated formal name. -/
def symbolEntries (scope : List (Resolved Formula)) : List (Name × Name) :=
  (scope.map Resolved.symbolReplacement).filter (fun entry => decide (entry.1 ≠ entry.2))

/-- Source Map iteration presents each unique formal key in ascending name order. -/
def symbolMap (scope : List (Resolved Formula)) : List (Name × Name) :=
  let entries := symbolEntries scope
  (((entries.map Prod.fst).eraseDups).mergeSort (fun left right => compare left right != .gt)).map
    (fun name => (name, (entries.lookup name).getD name))

/-- Rename a literal symbol and its annotation using the same simultaneous scope. -/
def renameRoot (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) (label : Label Formula) : Label Formula :=
  scopes.foldl (fun label scope =>
    ((symbolEntries scope).lookup label.1 |>.getD label.1, formulas.substitute (symbolMap scope) label.2)) label

/-- Structural substitution changes labels only and never splices in an actual subtree. -/
def renameTree (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) :
    Language.Term (Label Formula) → Language.Term (Label Formula)
  | .node label children => .node (renameRoot formulas scopes label) (children.map (renameTree formulas scopes))

/-- Observe one complete constructor node, whose leafness is never Mixed. -/
def rootObservation : Language.Term (Label Formula) → Observed Formula
  | .node label children => ⟨label.1, label.2, if children.isEmpty then .leaf else .inner⟩

/-- Complete-term observations use exactly the requested path when it exists. -/
def observe (term : Language.Term (Label Formula)) (path : Path) : Option (Observed Formula) :=
  (Language.Term.atPath term path).map rootObservation

/-- The source sparse comparison cases, after both root labels have been substituted. -/
def compareObserved [DecidableEq Formula] (left right : Observed Formula) : Option Bool :=
  if (left.name, left.refinement) ≠ (right.name, right.refinement) then some false
  else match left.leafness, right.leafness with
    | .leaf, .leaf => some true
    | .leaf, .inner | .inner, .leaf => some false
    | _, _ => none

/-- A source substitution leaves the observed leafness unchanged. -/
def renameObserved (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) (observed : Observed Formula) : Observed Formula :=
  let label := renameRoot formulas scopes (observed.name, observed.refinement)
  ⟨label.1, label.2, observed.leafness⟩

/-- The sparse source equality callback does not invent a subtree identity. -/
def sameShape [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (scopes : List (List (Resolved Formula))) (left right : Path) : Option Bool := do
  let left ← observed left
  let right ← observed right
  compareObserved (renameObserved formulas scopes left) (renameObserved formulas scopes right)

/-- Complete structural comparison renames every symbol before checking complete tree equality. -/
def sameTerm [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (scopes : List (List (Resolved Formula))) (left right : Path) : Option Bool := do
  let left ← Language.Term.atPath term left
  let right ← Language.Term.atPath term right
  pure (Language.termEq (renameTree formulas scopes left) (renameTree formulas scopes right))

/-- Renaming a complete tree gives exactly the renamed root observation, including its unchanged shape. -/
theorem root_rename (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) (term : Language.Term (Label Formula)) :
    rootObservation (renameTree formulas scopes term) = renameObserved formulas scopes (rootObservation term) := by
  cases term with
  | node label children => simp [renameTree, rootObservation, renameObserved]

/-- Every decided comparison of exact root observations agrees with complete structural equality. -/
theorem compareObserved_sound [DecidableEq Formula] (left right : Language.Term (Label Formula)) (answer : Bool)
    (decided : compareObserved (rootObservation left) (rootObservation right) = some answer) :
    Language.termEq left right = answer := by
  cases left with
  | node leftLabel leftChildren =>
      cases right with
      | node rightLabel rightChildren =>
          by_cases labels : leftLabel = rightLabel
          · subst rightLabel
            cases leftChildren <;> cases rightChildren <;>
              simp [compareObserved, rootObservation] at decided
            all_goals subst answer
            · exact (Language.termEq_correct _ _).mpr rfl
            · apply Bool.eq_iff_iff.mpr
              simp only [Bool.false_eq_true, iff_false]
              intro equal
              have impossible := (Language.termEq_correct _ _).mp equal
              cases impossible
            · apply Bool.eq_iff_iff.mpr
              simp only [Bool.false_eq_true, iff_false]
              intro equal
              have impossible := (Language.termEq_correct _ _).mp equal
              cases impossible
          · have names : (leftLabel.1, leftLabel.2) ≠ (rightLabel.1, rightLabel.2) := by simpa only [Prod.eta] using labels
            have answerFalse : answer = false := by simpa [compareObserved, rootObservation, names] using decided.symm
            subst answer
            cases equal : Language.termEq (.node leftLabel leftChildren) (.node rightLabel rightChildren) with
            | false => rfl
            | true => exact False.elim (labels (Language.Term.node.inj ((Language.termEq_correct _ _).mp equal)).1)

/-- Sparse source Yes/No for an observed term remains correct after every simultaneous structural scope. -/
theorem sameShape_sound [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (scopes : List (List (Resolved Formula))) (left right : Path) (answer : Bool)
    (decided : sameShape formulas (observe term) scopes left right = some answer) :
    sameTerm formulas term scopes left right = some answer := by
  cases leftTerm : Language.Term.atPath term left with
  | none => simp [sameShape, observe, leftTerm] at decided
  | some first =>
      cases rightTerm : Language.Term.atPath term right with
      | none => simp [sameShape, observe, leftTerm, rightTerm] at decided
      | some second =>
          have exact : compareObserved (rootObservation (renameTree formulas scopes first))
              (rootObservation (renameTree formulas scopes second)) = some answer := by
            simpa [sameShape, observe, leftTerm, rightTerm, root_rename] using decided
          simpa [sameTerm, leftTerm, rightTerm] using
            congrArg some (compareObserved_sound _ _ answer exact)

/-- Inner nodes with equal labels do not give a positive sparse identity result. -/
theorem inner_unknown [DecidableEq Formula] (name : Name) (refinement : Formula) :
    compareObserved ⟨name, refinement, .inner⟩ ⟨name, refinement, .inner⟩ = none := by
  simp [compareObserved]

/-- Mixed observations cannot prove identity even when their root labels agree. -/
theorem mixed_unknown [DecidableEq Formula] (name : Name) (refinement : Formula) (leafness : Leafness) :
    compareObserved ⟨name, refinement, .mixed⟩ ⟨name, refinement, leafness⟩ = none := by
  cases leafness <;> simp [compareObserved]

/-- The public sparse evaluator uses only the source observation-based equality callback. -/
def evaluateGuardWithShape [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (guard : SourceGuards.Guard Formula) : Guards.Verdict :=
  evaluateGuardWithSame formulas solver observed (sameShape formulas observed) guard

/-- The public complete-term evaluator uses actual equality after every structural name scope. -/
def evaluateGuard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : SourceGuards.Guard Formula) (term : Language.Term (Label Formula)) : Guards.Verdict :=
  evaluateGuardWithSame formulas solver (observe term) (sameTerm formulas term) guard

end MicroCFTA.SourceObservations
