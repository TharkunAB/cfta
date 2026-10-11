import MicroCFTA.FormulaLowering

/-!
# Full-syntax simplifier correctness

The simplifier follows the current source cases. It does not simplify inside
quantifiers or arithmetic terms. The comparison used to sort conjunctions is
a parameter: semantic preservation holds for every comparison, including the
source `Ord` comparison. Equality and duplicate removal are structural.
-/

namespace MicroCFTA.FormulaSimplify

open FullSyntax

noncomputable section
local instance : DecidableEq Term := Classical.typeDecidableEq _
local instance : DecidableEq Formula := Classical.typeDecidableEq _

/-- The primitive relation laws used by the source's exact syntactic tests. -/
structure RelationLaws (model : Interpretation Value) : Prop where
  eq_self : ∀ value, model.relation .eq value value
  ne_self : ∀ value, ¬model.relation .ne value value
  le_self : ∀ value, model.relation .le value value
  ge_self : ∀ value, model.relation .ge value value
  eq_literals : ∀ left right : Int, left ≠ right → ¬model.relation .eq (model.literal left) (model.literal right)
  ne_literals : ∀ left right : Int, left ≠ right → model.relation .ne (model.literal left) (model.literal right)

/-- The exact incomplete syntactic tautology test from the source. -/
def tautology : Formula → Bool
  | .top => true
  | .atom .eq left right | .atom .le left right | .atom .ge left right => decide (left = right)
  | .atom .ne (.lit left) (.lit right) => left != right
  | _ => false

/-- The exact incomplete syntactic contradiction test from the source. -/
def contradiction : Formula → Bool
  | .bottom => true
  | .atom .eq (.lit left) (.lit right) => left != right
  | .atom .ne left right => decide (left = right)
  | _ => false

/-- Every recognized tautology holds for all primitive interpretations that satisfy the relation laws. -/
theorem tautology_sound (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (p : Formula) (yes : tautology p = true) : Holds model env p := by
  cases p with
  | top => simp [Holds]
  | and _ | bottom | or _ | not _ | «forall» _ _ | «exists» _ _ => simp [tautology] at yes
  | atom relation left right =>
      cases relation with
      | eq => simp only [tautology, decide_eq_true_eq] at yes; subst right
              simpa [Holds] using laws.eq_self (evaluateTerm model env left)
      | le => simp only [tautology, decide_eq_true_eq] at yes; subst right
              simpa [Holds] using laws.le_self (evaluateTerm model env left)
      | ge => simp only [tautology, decide_eq_true_eq] at yes; subst right
              simpa [Holds] using laws.ge_self (evaluateTerm model env left)
      | gt | lt => simp [tautology] at yes
      | ne =>
          cases left <;> cases right <;> simp only [tautology, Bool.false_eq_true] at yes
          all_goals try contradiction
          rename_i left right
          have apart : left ≠ right := by simpa using yes
          simpa [Holds, evaluateTerm] using laws.ne_literals left right apart

/-- Every recognized contradiction is false under the same explicit relation laws. -/
theorem contradiction_sound (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (p : Formula) (yes : contradiction p = true) : ¬Holds model env p := by
  cases p with
  | bottom => simp [Holds]
  | top | and _ | or _ | not _ | «forall» _ _ | «exists» _ _ => simp [contradiction] at yes
  | atom relation left right =>
      cases relation with
      | ne => simp only [contradiction, decide_eq_true_eq] at yes; subst right
              simpa [Holds] using laws.ne_self (evaluateTerm model env left)
      | gt | ge | lt | le => simp [contradiction] at yes
      | eq =>
          cases left <;> cases right <;> simp only [contradiction, Bool.false_eq_true] at yes
          all_goals try contradiction
          rename_i left right
          have apart : left ≠ right := by simpa using yes
          simpa [Holds, evaluateTerm] using laws.eq_literals left right apart

/-- Conjunction truth is universal membership truth. -/
theorem all_iff (model : Interpretation Value) (env : Name → Value) (parts : List Formula) :
    holdsAll model env parts ↔ ∀ part ∈ parts, Holds model env part := by
  induction parts with
  | nil => simp [holdsAll]
  | cons part rest ih => simp [holdsAll, ih]

/-- Disjunction truth is existential membership truth. -/
theorem any_iff (model : Interpretation Value) (env : Name → Value) (parts : List Formula) :
    holdsAny model env parts ↔ ∃ part ∈ parts, Holds model env part := by
  induction parts with
  | nil => simp [holdsAny]
  | cons part rest ih => simp [holdsAny, ih]

theorem any_contradiction (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (parts : List Formula) (yes : parts.any contradiction = true) : ¬holdsAll model env parts := by
  rcases List.any_eq_true.mp yes with ⟨part, member, falsePart⟩
  intro all
  exact contradiction_sound model laws env part falsePart ((all_iff model env parts).mp all part member)

theorem any_tautology (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (parts : List Formula) (yes : parts.any tautology = true) : holdsAny model env parts := by
  rcases List.any_eq_true.mp yes with ⟨part, member, truePart⟩
  exact (any_iff model env parts).mpr ⟨part, member, tautology_sound model laws env part truePart⟩

theorem filter_tautology (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (parts : List Formula) :
    holdsAll model env (parts.filter fun part => !tautology part) ↔ holdsAll model env parts := by
  induction parts with
  | nil => simp [holdsAll]
  | cons part rest ih =>
      cases test : tautology part <;>
        simp [test, holdsAll, ih, tautology_sound model laws env part]

theorem filter_contradiction (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (parts : List Formula) :
    holdsAny model env (parts.filter fun part => !contradiction part) ↔ holdsAny model env parts := by
  induction parts with
  | nil => simp [holdsAny]
  | cons part rest ih =>
      cases test : contradiction part <;>
        simp [test, holdsAny, ih, contradiction_sound model laws env part]

/-- Flatten nested conjunctions and retain every other formula as a part. -/
def flatten : List Formula → List Formula
  | [] => []
  | .and parts :: rest => flatten parts ++ flatten rest
  | part :: rest => part :: flatten rest
termination_by parts => sizeOf parts

theorem all_append (model : Interpretation Value) (env : Name → Value) (left right : List Formula) :
    holdsAll model env (left ++ right) ↔ holdsAll model env left ∧ holdsAll model env right := by
  simp only [all_iff, List.mem_append]
  constructor
  · intro all
    exact ⟨fun part member => all part (Or.inl member), fun part member => all part (Or.inr member)⟩
  · rintro ⟨hl, hr⟩ part (member | member)
    · exact hl part member
    · exact hr part member

theorem flatten_semantics (model : Interpretation Value) (env : Name → Value) (parts : List Formula) :
    holdsAll model env (flatten parts) ↔ holdsAll model env parts := by
  cases parts with
  | nil => simp [flatten]
  | cons part rest =>
      cases part with
      | and nested => simp [flatten, holdsAll, Holds, all_append,
          flatten_semantics model env nested, flatten_semantics model env rest]
      | _ => simp [flatten, holdsAll, flatten_semantics model env rest]
termination_by sizeOf parts

/-- A sorted, structurally unique conjunction list. Its meaning is independent of the supplied comparison. -/
def canonical (compare : Formula → Formula → Bool) (parts : List Formula) : List Formula :=
  parts.eraseDups.mergeSort compare

theorem canonical_members (compare : Formula → Formula → Bool) (parts : List Formula) (part : Formula) :
    part ∈ canonical compare parts ↔ part ∈ parts := by simp [canonical]

theorem canonical_semantics (model : Interpretation Value) (env : Name → Value)
    (compare : Formula → Formula → Bool) (parts : List Formula) :
    holdsAll model env (canonical compare parts) ↔ holdsAll model env parts := by
  simp only [all_iff, canonical_members]

/-- Conjunction packing follows the source's empty and singleton cases. -/
def packAnd : List Formula → Formula
  | [] => .top
  | [part] => part
  | parts => .and parts

/-- Disjunction packing preserves the source's remaining `Or` wrapper. -/
def packOr : List Formula → Formula
  | [] => .bottom
  | parts => .or parts

/-- Eliminate one pair of adjacent negations. -/
def simplifyNot : Formula → Formula
  | .not part => part
  | part => .not part

theorem packAnd_semantics (model : Interpretation Value) (env : Name → Value) (parts : List Formula) :
    Holds model env (packAnd parts) ↔ holdsAll model env parts := by
  cases parts with
  | nil => simp [packAnd, Holds, holdsAll]
  | cons part rest => cases rest <;> simp [packAnd, Holds, holdsAll]

theorem packOr_semantics (model : Interpretation Value) (env : Name → Value) (parts : List Formula) :
    Holds model env (packOr parts) ↔ holdsAny model env parts := by
  cases parts <;> simp [packOr, Holds, holdsAny]

theorem simplifyNot_semantics (model : Interpretation Value) (env : Name → Value) (part : Formula) :
    Holds model env (simplifyNot part) ↔ ¬Holds model env part := by
  classical
  cases part <;> simp [simplifyNot, Holds]

mutual
/-- The complete source simplifier, parameterized only by conjunction sort order. -/
def simplify (compare : Formula → Formula → Bool) : Formula → Formula
  | .or [] => .bottom
  | .or [part] => simplify compare part
  | .not part => simplifyNot (simplify compare part)
  | .and parts =>
      if parts.any contradiction then .bottom
      else packAnd (canonical compare (flatten ((simplifyParts compare parts).filter fun part => !tautology part)))
  | .or parts =>
      if parts.any tautology then .top
      else packOr ((simplifyParts compare parts).filter fun part => !contradiction part)
  | part => if contradiction part then .bottom else if tautology part then .top else part
termination_by part => sizeOf part

/-- Simplify Boolean list parts before the source's list-specific operations. -/
def simplifyParts (compare : Formula → Formula → Bool) : List Formula → List Formula
  | [] => []
  | part :: rest => simplify compare part :: simplifyParts compare rest
termination_by parts => sizeOf parts
end

mutual
/-- Full-syntax simplification preserves truth for every interpretation satisfying the explicit relation laws. -/
theorem simplify_semantics (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (compare : Formula → Formula → Bool) (part : Formula) :
    Holds model env (simplify compare part) ↔ Holds model env part := by
  cases part with
  | top => simp [simplify, contradiction, tautology, Holds]
  | bottom => simp [simplify, contradiction, Holds]
  | not part => simp [simplify, Holds, simplifyNot_semantics, simplify_semantics model laws env compare part]
  | and parts =>
      simp only [simplify]
      split
      · rename_i yes
        simp [Holds, any_contradiction model laws env parts yes]
      · simp [packAnd_semantics, canonical_semantics, flatten_semantics, filter_tautology model laws,
          (parts_semantics model laws env compare parts).1, Holds]
  | or parts =>
      cases parts with
      | nil => simp [simplify, Holds, holdsAny]
      | cons part rest =>
          cases rest with
          | nil => simp [simplify, Holds, holdsAny, simplify_semantics model laws env compare part]
          | cons next rest =>
              simp only [simplify]
              split
              · rename_i yes
                simp [Holds, any_tautology model laws env (part :: next :: rest) yes]
              · simp [packOr_semantics, filter_contradiction model laws,
                  (parts_semantics model laws env compare (part :: next :: rest)).2, Holds]
  | atom relation left right =>
      simp only [simplify]
      split
      · rename_i yes
        simp [Holds, contradiction_sound model laws env (.atom relation left right) yes]
      · split
        · rename_i yes
          simp [Holds, tautology_sound model laws env (.atom relation left right) yes]
        · rfl
  | «forall» bound inner | «exists» bound inner => simp [simplify, tautology, contradiction]
termination_by sizeOf part

/-- List simplification preserves both Boolean folds. -/
theorem parts_semantics (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (compare : Formula → Formula → Bool) (parts : List Formula) :
    (holdsAll model env (simplifyParts compare parts) ↔ holdsAll model env parts) ∧
      (holdsAny model env (simplifyParts compare parts) ↔ holdsAny model env parts) := by
  cases parts with
  | nil => simp [simplifyParts]
  | cons part rest =>
      have hp := simplify_semantics model laws env compare part
      have hs := parts_semantics model laws env compare rest
      simp only [simplifyParts, holdsAll, holdsAny, hp, hs.1, hs.2, iff_self, and_self]
termination_by sizeOf parts
end

/-- The public conjunction constructor runs the proved source simplifier. -/
def conjunction (compare : Formula → Formula → Bool) (parts : List Formula) : Formula :=
  simplify compare (.and parts)

/-- The public disjunction constructor runs the proved source simplifier. -/
def disjunction (compare : Formula → Formula → Bool) (parts : List Formula) : Formula :=
  simplify compare (.or parts)

/-- The public implication constructor leaves its Boolean encoding unsimplified. -/
def implies (premise conclusion : Formula) : Formula := .or [.not premise, conclusion]

/-- The public equivalence constructor preserves its two source conjunctions. -/
def iff (left right : Formula) : Formula := .or [.and [left, right], .and [.not left, .not right]]

/-- Conjunction contains all and only the assignments satisfying every supplied part. -/
theorem conjunction_semantics (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (compare : Formula → Formula → Bool) (parts : List Formula) :
    Holds model env (conjunction compare parts) ↔ ∀ part ∈ parts, Holds model env part := by
  exact (simplify_semantics model laws env compare (.and parts)).trans
    (by simpa [Holds] using all_iff model env parts)

/-- Disjunction contains all and only the assignments satisfying at least one supplied part. -/
theorem disjunction_semantics (model : Interpretation Value) (laws : RelationLaws model)
    (env : Name → Value) (compare : Formula → Formula → Bool) (parts : List Formula) :
    Holds model env (disjunction compare parts) ↔ ∃ part ∈ parts, Holds model env part := by
  exact (simplify_semantics model laws env compare (.or parts)).trans
    (by simpa [Holds] using any_iff model env parts)

/-- The source implication encoding has ordinary classical implication semantics. -/
theorem implies_semantics (model : Interpretation Value) (env : Name → Value) (premise conclusion : Formula) :
    Holds model env (implies premise conclusion) ↔ (Holds model env premise → Holds model env conclusion) := by
  classical
  by_cases hp : Holds model env premise <;> simp [implies, Holds, holdsAny, hp]

/-- The source equivalence encoding has ordinary classical equivalence semantics. -/
theorem iff_semantics (model : Interpretation Value) (env : Name → Value) (left right : Formula) :
    Holds model env (iff left right) ↔ (Holds model env left ↔ Holds model env right) := by
  classical
  by_cases hl : Holds model env left <;> by_cases hr : Holds model env right <;>
    simp [iff, Holds, holdsAll, holdsAny, hl, hr]

/-- Full-syntax simplification remains sound after the actual target lowering. -/
theorem simplify_lower (model : FormulaLowering.Model Value) (laws : RelationLaws (FormulaLowering.sourceModel model))
    (env : Name → Value) (compare : Formula → Formula → Bool) (part : Formula) :
    FormulaLowering.Holds model env (FormulaLowering.lowerFormula (simplify compare part)) ↔
      FormulaLowering.Holds model env (FormulaLowering.lowerFormula part) := by
  exact (FormulaLowering.formula_lower model _ env).trans
    ((simplify_semantics (FormulaLowering.sourceModel model) laws env compare part).trans
      (FormulaLowering.formula_lower model part env).symm)

end
end MicroCFTA.FormulaSimplify
