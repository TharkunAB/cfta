import MicroCFTA.SolverAdapter

/-!
# Name encoding and complete quantified query meaning

One injective encoding applies to declarations, variable occurrences,
function heads, and binders. It preserves repeated-binder shadowing and
all mixed-sort meanings. No surjectivity assumption is required.
-/
namespace MicroCFTA.SourceSolverNameSemantics
open FormulaLowering
open FullSyntax (Name update)

mutual
/-- Encode every name in the emitted value expression. -/
def renameTerm (rename : Name → Name) : Term → Term
  | .integer value => .integer value
  | .variable name => .variable (rename name)
  | .negative inner => .negative (renameTerm rename inner)
  | .binary operator left right => .binary operator (renameTerm rename left) (renameTerm rename right)
  | .application function argument => .application (renameTerm rename function) (renameTerm rename argument)
  | .conditional condition yes no => .conditional (renameFormula rename condition) (renameTerm rename yes) (renameTerm rename no)
  | .cast inner sort => .cast (renameTerm rename inner) sort
termination_by term => sizeOf term

/-- Encode all predicate names, including every bound declaration. -/
def renameFormula (rename : Name → Name) : Formula → Formula
  | .true => .true
  | .false => .false
  | .and parts => .and (renameParts rename parts)
  | .or parts => .or (renameParts rename parts)
  | .not inner => .not (renameFormula rename inner)
  | .atom relation left right => .atom relation (renameTerm rename left) (renameTerm rename right)
  | .forall bound inner => .forall (bound.map fun binding => (rename binding.1, binding.2)) (renameFormula rename inner)
  | .exists bound inner => .exists (bound.map fun binding => (rename binding.1, binding.2)) (renameFormula rename inner)
termination_by formula => sizeOf formula

/-- Retain the order of encoded Boolean parts. -/
def renameParts (rename : Name → Name) : List Formula → List Formula
  | [] => []
  | first :: rest => renameFormula rename first :: renameParts rename rest
termination_by parts => sizeOf parts
end

/-- Encoded updates change exactly the original bound name. -/
theorem update_comp (rename : Name → Name) (injective : Function.Injective rename)
    (env : Name → Value) (name : Name) (value : Value) :
    (update env (rename name) value) ∘ rename = update (env ∘ rename) name value := by
  funext other
  simp only [Function.comp_def, update, injective.eq_iff]

/-- Universal binder traversal commutes with injective encoding. -/
theorem allBound_rename (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (bound : List (Name × TargetSort)) (encodedBody body : (Name → Value) → Prop)
    (exactBody : ∀ env, encodedBody env ↔ body (env ∘ rename)) (env : Name → Value) :
    allBound model (bound.map fun binding => (rename binding.1, binding.2)) env encodedBody ↔
      allBound model bound (env ∘ rename) body := by
  induction bound generalizing env with
  | nil => exact exactBody env
  | cons binding rest ih =>
    simp only [List.map_cons, allBound]
    apply forall_congr'
    intro value
    apply imp_congr_right
    intro _
    rw [ih, update_comp rename injective]

/-- Existential binder traversal retains the same witnesses and shadowing. -/
theorem someBound_rename (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (bound : List (Name × TargetSort)) (encodedBody body : (Name → Value) → Prop)
    (exactBody : ∀ env, encodedBody env ↔ body (env ∘ rename)) (env : Name → Value) :
    someBound model (bound.map fun binding => (rename binding.1, binding.2)) env encodedBody ↔
      someBound model bound (env ∘ rename) body := by
  induction bound generalizing env with
  | nil => exact exactBody env
  | cons binding rest ih =>
    simp only [List.map_cons, someBound]
    apply exists_congr
    intro value
    apply and_congr_right
    intro _
    rw [ih, update_comp rename injective]

mutual
/-- Encoded terms retain every primitive value, including function application. -/
theorem term_meaning (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (term : Term) (env : Name → Value) :
    evaluate model env (renameTerm rename term) = evaluate model (env ∘ rename) term := by
  cases term with
  | integer _ | «variable» _ => simp only [renameTerm, evaluate, Function.comp_def]
  | negative inner => simp only [renameTerm, evaluate, term_meaning model rename injective inner]
  | binary operator left right | application left right =>
    simp only [renameTerm, evaluate, term_meaning model rename injective left, term_meaning model rename injective right]
  | conditional condition yes no =>
    simp only [renameTerm, evaluate,
      term_meaning model rename injective yes, term_meaning model rename injective no]
    rw [propext (formula_meaning model rename injective condition env)]
  | cast inner sort => simp only [renameTerm, evaluate, term_meaning model rename injective inner]
termination_by sizeOf term

/-- Every quantified mixed-sort formula has unchanged meaning under the name encoding. -/
theorem formula_meaning (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (formula : Formula) (env : Name → Value) :
    Holds model env (renameFormula rename formula) ↔ Holds model (env ∘ rename) formula := by
  cases formula with
  | true | false => simp only [renameFormula, Holds]
  | and parts => simpa only [renameFormula, Holds] using (parts_meaning model rename injective parts env).1
  | or parts => simpa only [renameFormula, Holds] using (parts_meaning model rename injective parts env).2
  | not inner => simpa only [renameFormula, Holds] using not_congr (formula_meaning model rename injective inner env)
  | atom relation left right =>
    simp only [renameFormula, Holds, term_meaning model rename injective left, term_meaning model rename injective right]
  | «forall» bound inner =>
    simp only [renameFormula, Holds]
    exact allBound_rename model rename injective bound
      (fun assigned => Holds model assigned (renameFormula rename inner))
      (fun assigned => Holds model assigned inner) (formula_meaning model rename injective inner) env
  | «exists» bound inner =>
    simp only [renameFormula, Holds]
    exact someBound_rename model rename injective bound
      (fun assigned => Holds model assigned (renameFormula rename inner))
      (fun assigned => Holds model assigned inner) (formula_meaning model rename injective inner) env
termination_by sizeOf formula

/-- Conjunction and disjunction retain every encoded part in order. -/
theorem parts_meaning (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (parts : List Formula) (env : Name → Value) :
    (holdsAll model env (renameParts rename parts) ↔ holdsAll model (env ∘ rename) parts) ∧
      (holdsAny model env (renameParts rename parts) ↔ holdsAny model (env ∘ rename) parts) := by
  cases parts with
  | nil => simp only [renameParts, holdsAll, holdsAny, iff_self, and_self]
  | cons first rest =>
    simp only [renameParts, holdsAll, holdsAny, formula_meaning model rename injective first,
      (parts_meaning model rename injective rest env).1, (parts_meaning model rename injective rest env).2,
      iff_self, and_self]
termination_by sizeOf parts
end

/-- Encode declarations with the same symbol map as the complete assertion. -/
def renamePrepared (rename : Name → Name) (request : SolverAdapter.Prepared) : SolverAdapter.Prepared :=
  ⟨request.declared.map fun binding => (rename binding.1, binding.2), renameFormula rename request.asserted⟩

/-- Declaration domains transport through the same encoding, including duplicate declarations. -/
theorem admitted_rename (model : Model Value) (rename : Name → Name)
    (declared : List SolverAdapter.Declaration) (env : Name → Value) :
    SolverAdapter.Admitted model (declared.map fun binding => (rename binding.1, binding.2)) env ↔
      SolverAdapter.Admitted model declared (env ∘ rename) := by
  simp only [SolverAdapter.Admitted, List.forall_mem_map, Function.comp_def]

open Classical in
/-- Extend any source environment to encoded names; names outside the image are irrelevant. -/
noncomputable def extend (rename : Name → Name) (env : Name → Value) : Name → Value :=
  fun encoded => if found : ∃ name, rename name = encoded then env (Classical.choose found) else env ""

/-- The extension reads every original name exactly. -/
theorem extend_comp (rename : Name → Name) (injective : Function.Injective rename) (env : Name → Value) :
    extend rename env ∘ rename = env := by
  funext name
  classical
  simp only [Function.comp_def, extend]
  have found : ∃ original, rename original = rename name := ⟨name, rfl⟩
  rw [dite_eq_left found]
  rw [injective (Classical.choose_spec found)]

/-- Encoding preserves satisfiability in both directions, not just valid-query soundness. -/
theorem satisfiable_rename (model : Model Value) (rename : Name → Name) (injective : Function.Injective rename)
    (request : SolverAdapter.Prepared) :
    (∃ env, SolverAdapter.Admitted model (renamePrepared rename request).declared env ∧
      Holds model env (renamePrepared rename request).asserted) ↔
    ∃ env, SolverAdapter.Admitted model request.declared env ∧ Holds model env request.asserted := by
  simp only [renamePrepared, admitted_rename, formula_meaning model rename injective]
  constructor
  · rintro ⟨env, domain, holds⟩
    exact ⟨env ∘ rename, domain, holds⟩
  · rintro ⟨env, domain, holds⟩
    refine ⟨extend rename env, ?_, ?_⟩
    · simpa only [extend_comp rename injective] using domain
    · simpa only [extend_comp rename injective] using holds

/-- Encoded counterexample queries decide the same intended declared-domain entailment. -/
theorem encoded_unsat_iff_entails (model : Model Value) (rename : Name → Name)
    (injective : Function.Injective rename) (declared : List SolverAdapter.Declaration)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) :
    (¬∃ env, SolverAdapter.Admitted model (renamePrepared rename ⟨declared,
      SolverAdapter.assertion assumptions antecedent consequent⟩).declared env ∧
      Holds model env (renamePrepared rename ⟨declared,
        SolverAdapter.assertion assumptions antecedent consequent⟩).asserted) ↔
      SolverAdapter.Entails model declared assumptions antecedent consequent := by
  rw [satisfiable_rename model rename injective]
  exact SolverAdapter.unsat_iff_entails model declared assumptions antecedent consequent

end MicroCFTA.SourceSolverNameSemantics
