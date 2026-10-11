import MicroCFTA.FullSyntax

/-!
# Semantics of every sorted formula constructor

These proofs apply to every interpretation of the primitive operations and
sort domains. They include quantifiers, function names, division, modulo,
casts, and conditional terms. They do not assume a solver decision procedure.
-/

namespace MicroCFTA.FormulaSemantics

open FullSyntax

/-- Two environments agree on a finite collection of names. -/
def Agree (names : List Name) (left right : Name → Value) : Prop :=
  ∀ name ∈ names, left name = right name

/-- Assignment of one common bound value preserves agreement outside the other binders. -/
theorem update_agree (names : List Name) (bound : List (Name × ValueSort))
    (left right : Name → Value) (name : Name) (sort : ValueSort) (value : Value)
    (agree : ∀ x ∈ names, x ∉ ((name, sort) :: bound).map Prod.fst → left x = right x) :
    ∀ x ∈ names, x ∉ bound.map Prod.fst → update left name value x = update right name value x := by
  intro x member outside
  by_cases same : x = name
  · simp [update, same]
  · simpa [update, same] using agree x member (by simpa [same] using outside)

/-- Universal binders preserve body equivalence under agreement on free names. -/
theorem allBound_congr (model : Interpretation Value) (bound : List (Name × ValueSort))
    (names : List Name) (left right : Name → Value) (body other : (Name → Value) → Prop)
    (congruent : ∀ a b, Agree names a b → (body a ↔ other b))
    (agree : ∀ name ∈ names, name ∉ bound.map Prod.fst → left name = right name) :
    allBound model bound left body ↔ allBound model bound right other := by
  induction bound generalizing left right with
  | nil => exact congruent left right (fun name member => agree name member (by simp))
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [allBound]
      apply forall_congr'
      intro value
      apply imp_congr_right
      intro _
      exact ih (update left name value) (update right name value)
        (update_agree names rest left right name sort value agree)

/-- Existential binders preserve body equivalence under agreement on free names. -/
theorem someBound_congr (model : Interpretation Value) (bound : List (Name × ValueSort))
    (names : List Name) (left right : Name → Value) (body other : (Name → Value) → Prop)
    (congruent : ∀ a b, Agree names a b → (body a ↔ other b))
    (agree : ∀ name ∈ names, name ∉ bound.map Prod.fst → left name = right name) :
    someBound model bound left body ↔ someBound model bound right other := by
  induction bound generalizing left right with
  | nil => exact congruent left right (fun name member => agree name member (by simp))
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [someBound]
      apply exists_congr
      intro value
      apply and_congr_right
      intro _
      exact ih (update left name value) (update right name value)
        (update_agree names rest left right name sort value agree)

mutual
/-- A term depends only on its syntactic free names, for every primitive interpretation. -/
theorem term_ext (model : Interpretation Value) (t : Term) (left right : Name → Value)
    (agree : Agree (termNames t) left right) :
    evaluateTerm model left t = evaluateTerm model right t := by
  cases t with
  | lit n => simp [evaluateTerm]
  | var name => simpa [evaluateTerm] using agree name (by simp [termNames])
  | app name args =>
      simp only [evaluateTerm]
      rw [agree name (by simp [termNames])]
      rw [arguments_ext model args left right (fun n hn => agree n (by simp [termNames, hn]))]
  | neg t =>
      simp only [evaluateTerm]
      rw [term_ext model t left right (by simpa [termNames] using agree)]
  | add t u | sub t u | mul t u | div t u | mod t u =>
      have ht := term_ext model t left right (fun n hn => agree n (by simp [termNames, hn]))
      have hu := term_ext model u left right (fun n hn => agree n (by simp [termNames, hn]))
      simp only [evaluateTerm, ht, hu]
  | ite p t u =>
      have hp := formula_ext model p left right (fun n hn => agree n (by simp [termNames, hn]))
      have ht := term_ext model t left right (fun n hn => agree n (by simp [termNames, hn]))
      have hu := term_ext model u left right (fun n hn => agree n (by simp [termNames, hn]))
      simp only [evaluateTerm, ht, hu]
      by_cases h : Holds model left p
      · simp [h, hp.mp h]
      · have hn : ¬Holds model right p := fun yes => h (hp.mpr yes)
        simp [h, hn]
  | cast t sort =>
      simp only [evaluateTerm]
      rw [term_ext model t left right (by simpa [termNames] using agree)]
termination_by sizeOf t

/-- An argument vector depends only on its free names, with order preserved. -/
theorem arguments_ext (model : Interpretation Value) (args : List Term) (left right : Name → Value)
    (agree : Agree (argumentsNames args) left right) :
    evaluateTerms model left args = evaluateTerms model right args := by
  cases args with
  | nil => simp [evaluateTerms]
  | cons t ts =>
      have ht := term_ext model t left right (fun n hn => agree n (by simp [argumentsNames, hn]))
      have hs := arguments_ext model ts left right (fun n hn => agree n (by simp [argumentsNames, hn]))
      simp only [evaluateTerms, ht, hs]
termination_by sizeOf args

/-- A complete sorted formula depends only on its free names. -/
theorem formula_ext (model : Interpretation Value) (p : Formula) (left right : Name → Value)
    (agree : Agree (formulaNames p) left right) :
    Holds model left p ↔ Holds model right p := by
  cases p with
  | top | bottom => simp [Holds]
  | and ps => simpa [Holds] using all_ext model ps left right (by simpa [formulaNames] using agree)
  | or ps => simpa [Holds] using any_ext model ps left right (by simpa [formulaNames] using agree)
  | not p => simpa [Holds] using not_congr (formula_ext model p left right (by simpa [formulaNames] using agree))
  | atom relation t u =>
      have ht := term_ext model t left right (fun n hn => agree n (by simp [formulaNames, hn]))
      have hu := term_ext model u left right (fun n hn => agree n (by simp [formulaNames, hn]))
      simp only [Holds, ht, hu]
  | «forall» bound p =>
      simpa [Holds] using allBound_congr model bound (formulaNames p) left right (fun env => Holds model env p) (fun env => Holds model env p)
        (fun a b h => formula_ext model p a b h)
        (fun n hn hb => agree n (by simpa [formulaNames] using And.intro hn hb))
  | «exists» bound p =>
      simpa [Holds] using someBound_congr model bound (formulaNames p) left right (fun env => Holds model env p) (fun env => Holds model env p)
        (fun a b h => formula_ext model p a b h)
        (fun n hn hb => agree n (by simpa [formulaNames] using And.intro hn hb))
termination_by sizeOf p

/-- Conjunction truth depends only on its parts' free names. -/
theorem all_ext (model : Interpretation Value) (ps : List Formula) (left right : Name → Value)
    (agree : Agree (partsNames ps) left right) :
    holdsAll model left ps ↔ holdsAll model right ps := by
  cases ps with
  | nil => simp [holdsAll]
  | cons p ps =>
      have hp := formula_ext model p left right (fun n hn => agree n (by simp [partsNames, hn]))
      have hs := all_ext model ps left right (fun n hn => agree n (by simp [partsNames, hn]))
      simp only [holdsAll, hp, hs]
termination_by sizeOf ps

/-- Disjunction truth depends only on its parts' free names. -/
theorem any_ext (model : Interpretation Value) (ps : List Formula) (left right : Name → Value)
    (agree : Agree (partsNames ps) left right) :
    holdsAny model left ps ↔ holdsAny model right ps := by
  cases ps with
  | nil => simp [holdsAny]
  | cons p ps =>
      have hp := formula_ext model p left right (fun n hn => agree n (by simp [partsNames, hn]))
      have hs := any_ext model ps left right (fun n hn => agree n (by simp [partsNames, hn]))
      simp only [holdsAny, hp, hs]
termination_by sizeOf ps
end

/-- Updating an absent free name does not change a formula's meaning. -/
theorem absent_update (model : Interpretation Value) (env : Name → Value)
    (p : Formula) (name : Name) (value : Value) (absent : name ∉ formulaNames p) :
    Holds model (update env name value) p ↔ Holds model env p := by
  apply formula_ext
  intro other member
  have different : other ≠ name := by intro equal; subst other; exact absent member
  simp [update, different]

end MicroCFTA.FormulaSemantics
