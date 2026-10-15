import MicroCFTA.SourceSolverAppliedPreparation
import MicroCFTA.SourceSizedLiquidAmbient

/-!
# Full current declared domains with inferred integer functions

Explicit and generated declarations retain their original precedence.
Other free names receive the actual inferred function sort or Int. This
domain includes all source formula constructors and ambient assumptions.
-/
namespace MicroCFTA.SourceSizedLiquidAppliedAmbient
open FullSyntax SolverAdapter SourceSizedLiquidProgram
open SourceSizedLiquidAmbient (freshSpecs fresh_exact fresh_names)

/-- The current source domain retains every actual declaration restriction. -/
def Domain (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (env : Name → Value) : Prop :=
  (∀ binding ∈ declarations given, model.hasSort binding.2 (env binding.1)) ∧
  (∀ binding ∈ query.bindings,
    model.hasSort ((lookupSort binding.2 (declarations given)).getD .int) (env binding.1)) ∧
  (∀ name, (name ∈ formulaNames query.antecedent ∨ name ∈ formulaNames query.consequent ∨
      name ∈ partsNames assumptions) → name ∉ (declarations given).map Prod.fst →
      name ∉ query.bindings.map Prod.fst →
      model.hasSort (SourceAppliedDeclarations.inferredSort
        (SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent) name) (env name))

private theorem fresh_original (ambient : List Declaration) (assumptions : List Formula)
    (bindings : List (Name × Name)) (entries : List Declaration)
    (done : SourceSizedLiquidAmbientRepair.reservedFreshList ambient assumptions bindings = some entries) :
    freshDeclarations ambient bindings = some entries := by
  rw [SourceSizedLiquidAmbientRepair.reservedFreshList_exact] at done
  split at done
  · cases done
  · exact done

/-- Current preparation admits exactly the independently specified full source domain. -/
theorem prepared_domain (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (request : Prepared)
    (prepared : SourceSolverAppliedPreparation.prepare given assumptions query = some request)
    (env : Name → Value) : Admitted model request.declared env ↔ Domain model given assumptions query env := by
  cases fresh : SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings with
  | none => simp [SourceSolverAppliedPreparation.prepare, fresh] at prepared
  | some entries =>
      have entryEq := fresh_exact (declarations given) query.bindings entries
        (fresh_original _ _ _ _ fresh)
      simp [SourceSolverAppliedPreparation.prepare, fresh] at prepared
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
          apply admitted (name, SourceAppliedDeclarations.inferredSort
            (SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent) name)
          apply List.mem_append_right
          apply List.mem_append_right
          apply (SourceAppliedDeclarations.undeclared_exact _ _ _ _ _ _).mpr
          exact ⟨(mentioned_exact assumptions query.antecedent query.consequent name).mpr free,
            ambientAbsent, by simpa [fresh_names] using freshAbsent, rfl⟩
      · rintro ⟨ambient, generated, defaults⟩ binding member
        rcases List.mem_append.mp member with old | later
        · exact ambient binding old
        · rcases List.mem_append.mp later with freshMember | defaultMember
          · obtain ⟨source, present, same⟩ := List.mem_map.mp freshMember
            subst binding
            exact generated source present
          · have member := (SourceAppliedDeclarations.undeclared_exact _ _ _ _ _ _).mp defaultMember
            rw [member.2.2.2]
            exact defaults binding.1 ((mentioned_exact _ _ _ _).mp member.1) member.2.1
              (by simpa [fresh_names] using member.2.2.1)

/-- Successful preparation keeps the exact existing lowered assertion. -/
theorem prepared_assertion (given : List Declaration) (assumptions : List Formula) (query : Query)
    (request : Prepared) (prepared : SourceSolverAppliedPreparation.prepare given assumptions query = some request) :
    request.asserted = assertion assumptions query.antecedent query.consequent := by
  cases fresh : SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings with
  | none => simp [SourceSolverAppliedPreparation.prepare, fresh] at prepared
  | some entries =>
      simp [SourceSolverAppliedPreparation.prepare, fresh] at prepared
      subst request
      rfl

/-- Current entailment quantifies over the actual inferred declaration domains. -/
def Meaning (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) : Prop :=
  ∀ env, Domain model given assumptions query env →
    holdsAll (FormulaLowering.sourceModel model) env assumptions →
    Holds (FormulaLowering.sourceModel model) env query.antecedent →
    Holds (FormulaLowering.sourceModel model) env query.consequent

/-- Full current source preparation has the exact ambient declared-domain meaning. -/
theorem prepared_meaning (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (request : Prepared)
    (prepared : SourceSolverAppliedPreparation.prepare given assumptions query = some request) :
    SolverAdapter.Entails model request.declared assumptions query.antecedent query.consequent ↔
      Meaning model given assumptions query := by
  simp only [SolverAdapter.Entails, Meaning, prepared_domain model given assumptions query request prepared]

/-- The complete current encoded assertion is unsatisfiable exactly for the intended ambient entailment. -/
theorem encoded_unsat_iff_meaning (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (request : Prepared)
    (prepared : SourceSolverAppliedPreparation.encodedPrepare given assumptions query = some request) :
    (¬∃ env, Admitted model request.declared env ∧ FormulaLowering.Holds model env request.asserted) ↔
      Meaning model given assumptions query := by
  rw [SourceSolverAppliedPreparation.sourcePrepare_encode] at prepared
  obtain ⟨original, originalPrepared, same⟩ := Option.map_eq_some_iff.mp prepared
  subst request
  rw [SourceSolverNameSemantics.satisfiable_rename model _
    (fun _ _ equal => SourceSolverNameFastEncoding.encode_injective equal)]
  rw [prepared_assertion given assumptions query original originalPrepared]
  exact (SolverAdapter.unsat_iff_entails model original.declared assumptions query.antecedent query.consequent).trans
    (prepared_meaning model given assumptions query original originalPrepared)

/-- Application-free source domains retain every historical ambient restriction. -/
theorem app_free_domain (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List Formula) (query : Query) (env : Name → Value)
    (clear : SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent = []) :
    Domain model given assumptions query env ↔ SourceSizedLiquidAmbient.Domain model given assumptions query env := by
  simp only [Domain, SourceSizedLiquidAmbient.Domain, clear, SourceAppliedDeclarations.inferredSort,
    SourceAppliedDeclarations.lookupArity]

end MicroCFTA.SourceSizedLiquidAppliedAmbient
