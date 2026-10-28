          ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel result.2 caller memos.query
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) = outcome) ∧
      (∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        SourcePruningEnumerationOrigins.AssignmentOrigins whole after.counter assignment ↔
          SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment) ∧
      ∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol)
        (whole : Language.Term Symbol),
        Satisfies language meaning assignment before.core →
        Fragments.fill assignment fragment = assignment uv →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.OriginPolicies templates whole →
        SourcePruningEnumerationOrigins.Origin whole (assignment uv) →
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ∧
          result.1 = false ∧
          (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
          ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel result.2 caller memos.query
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) = outcome := by
  obtain ⟨fuel, result, after, outcome, retained⟩ := callback_finite_complete_resources_models
    holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
    checkEmpty edgesOf stop order recursiveFuel seed ceiling packet allocated bounded known
    selectionMembers selectionLength mass reserved
  refine ⟨fuel, result, after, outcome, retained, ?_, ?_⟩
  · intro whole assignment
    rw [retained.1.2.2.1.counter]
  intro language meaning assignment whole satisfied filled refuted policies origin
  have localPolicies := policies (assignment uv) origin
  have avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) := by
    simpa only [filled] using localPolicies.1
  have encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
      SourcePruningTemplates.ProgramEncoding program := by
    simpa only [filled] using localPolicies.2
  exact retained.2.2 language meaning assignment satisfied filled refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
