import MicroCFTA.SourceSizedLiquidAdapter

/-!
# Mixed declaration sorts and ambient Liquid assumptions

The environment domain preserves every ambient declaration, the inherited
sort of each generated value, and Int defaults for other free names. Ambient
assumptions restrict the entailment context. Guard substitutions do not
rename those assumptions. No all-Int or empty-assumption premise is used.
-/

namespace MicroCFTA.SourceSizedLiquidAmbient

open FullSyntax SolverAdapter SourceSizedLiquidProgram

/-- Generated values inherit the first declared sort of their originals, with the source Int default. -/
def freshSpecs (ambient : List Declaration) (bindings : List (Name × Name)) : List Declaration :=
  bindings.map fun binding => (binding.1, (lookupSort binding.2 ambient).getD .int)

/-- Successful fresh-name preflight returns exactly the independently specified sorts. -/
theorem fresh_exact (ambient : List Declaration) (bindings : List (Name × Name))
    (fresh : List Declaration) (completed : freshDeclarations ambient bindings = some fresh) :
    fresh = freshSpecs ambient bindings := by
  induction bindings generalizing fresh with
  | nil => simp [freshDeclarations] at completed; subst fresh; rfl
  | cons binding rest ih =>
      cases first : freshDeclaration ambient binding with
      | none => simp [freshDeclarations, first] at completed
      | some declaration =>
          cases tail : freshDeclarations ambient rest with
          | none => simp [freshDeclarations, first, tail] at completed
          | some remaining =>
              have equal : declaration :: remaining = fresh := by simpa [freshDeclarations, first, tail] using completed
              subst fresh
              have head : declaration = (binding.1, (lookupSort binding.2 ambient).getD .int) := by
                unfold freshDeclaration at first
                split at first
                · contradiction
                · exact (Option.some.inj first).symm
              simp [freshSpecs, head, ih remaining tail]

/-- The actual generated names are the binding targets, even when targets repeat. -/
theorem fresh_names (ambient : List Declaration) (bindings : List (Name × Name)) :
    (freshSpecs ambient bindings).map Prod.fst = bindings.map Prod.fst := by
  simp [freshSpecs, List.map_map, Function.comp_def]

/-- Independently specify all environmental sort restrictions of one complete query. -/
def Domain (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (env : Name → Value) : Prop :=
  (∀ binding ∈ declarations given, model.hasSort binding.2 (env binding.1)) ∧
  (∀ binding ∈ query.bindings,
    model.hasSort ((lookupSort binding.2 (declarations given)).getD .int) (env binding.1)) ∧
  (∀ name, (name ∈ formulaNames query.antecedent ∨ name ∈ formulaNames query.consequent ∨
      name ∈ partsNames assumptions) → name ∉ (declarations given).map Prod.fst →
      name ∉ query.bindings.map Prod.fst → model.hasSort .int (env name))

/-- The source prepared declarations admit exactly the independently specified environments. -/
theorem prepared_domain (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (request : Prepared)
    (prepared : prepareQuery given query.bindings assumptions query.antecedent query.consequent = some request)
    (env : Name → Value) : Admitted model request.declared env ↔ Domain model given assumptions query env := by
  cases fresh : freshDeclarations (declarations given) query.bindings with
  | none => simp [prepareQuery, prepare, fresh] at prepared
  | some entries =>
      have entryEq := fresh_exact (declarations given) query.bindings entries fresh
      simp [prepareQuery, prepare, fresh] at prepared
      subst request
      rw [entryEq]
      constructor
      · intro admitted
        refine ⟨?_, ?_, ?_⟩
        · intro binding member
          exact admitted binding (by simp [member])
        · intro binding member
          exact admitted (binding.1, (lookupSort binding.2 (declarations given)).getD .int)
            (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨binding, member, rfl⟩)))
        · intro name free ambientAbsent freshAbsent
          apply admitted (name, .int)
          apply List.mem_append_right
          apply List.mem_append_right
          apply (undeclared_exact _ _ _ name .int).mpr
          exact ⟨(mentioned_exact assumptions query.antecedent query.consequent name).mpr free,
            ambientAbsent, by simpa [fresh_names] using freshAbsent, rfl⟩
      · rintro ⟨ambient, generated, defaults⟩ binding member
        rcases List.mem_append.mp member with old | later
        · exact ambient binding old
        · rcases List.mem_append.mp later with freshMember | defaultMember
          · obtain ⟨source, present, same⟩ := List.mem_map.mp freshMember
            subst binding
            exact generated source present
          · have member := (undeclared_exact _ _ _ binding.1 binding.2).mp defaultMember
            rw [member.2.2.2]
            exact defaults binding.1 ((mentioned_exact _ _ _ _).mp member.1) member.2.1
              (by simpa [fresh_names] using member.2.2.1)

/-- Ambient assumptions restrict the mathematical implication; they are not substituted guard operands. -/
def Meaning (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) : Prop :=
  ∀ env, Domain model given assumptions query env →
    holdsAll (FormulaLowering.sourceModel model) env assumptions →
    Holds (FormulaLowering.sourceModel model) env query.antecedent →
    Holds (FormulaLowering.sourceModel model) env query.consequent

/-- The lowered SMT assertion has exactly the intended mixed-sort ambient entailment meaning. -/
theorem prepared_meaning (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (request : Prepared)
    (prepared : prepareQuery given query.bindings assumptions query.antecedent query.consequent = some request) :
    SolverAdapter.Entails model request.declared assumptions query.antecedent query.consequent ↔
      Meaning model given assumptions query := by
  simp only [SolverAdapter.Entails, Meaning, prepared_domain model given assumptions query request prepared]

/-- One withZ3Assuming query keeps its original ambient assumptions and actual result. -/
inductive Call (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) : Query → Nat → Result → Prop where
  | preflight : prepareQuery given query.bindings assumptions query.antecedent query.consequent = none →
      Call given assumptions milliseconds check query 1 (.returned .unknown)
  | checked : prepareQuery given query.bindings assumptions query.antecedent query.consequent = some request →
      check request work attempt →
      Call given assumptions milliseconds check query (work + 1) (finish milliseconds attempt).result

/-- Per-occurrence external Sat and Unsat correctness derives the full ambient-context query contract. -/
theorem call_supports (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    {query work result} (call : Call given assumptions milliseconds check query work result) :
    ResultSupports result (Meaning model given assumptions query) := by
  cases call with
  | preflight rejected => trivial
  | @checked request work attempt query prepared called =>
      cases attempt with
      | interrupted description => trivial
      | answered response reached =>
          have support := response_sound model request assumptions query.antecedent query.consequent
            (prepared_assertion given query.bindings assumptions query.antecedent query.consequent request prepared)
            milliseconds reached response (correct request work response reached called)
          have same := prepared_meaning model given assumptions query request prepared
          cases answer : responseVerdict milliseconds reached response with
          | raised err => simp only [finish, answer, ResultSupports]
          | returned verdict =>
              rw [answer] at support
              simpa only [finish, answer, ResultSupports] using
                SourceSizedLiquidLogical.supports_congr verdict same support

/-- Every completed external check gives a finite ambient adapter outcome, including exceptions. -/
theorem call_finite (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (query : Query) :
    ∃ work result, Call given assumptions milliseconds check query work result := by
  cases prepared : prepareQuery given query.bindings assumptions query.antecedent query.consequent with
  | none => exact ⟨1, .returned .unknown, .preflight prepared⟩
  | some request =>
      obtain ⟨work, attempt, called⟩ := completed request
      exact ⟨work + 1, (finish milliseconds attempt).result, .checked prepared called⟩

end MicroCFTA.SourceSizedLiquidAmbient
