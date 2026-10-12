import MicroCFTA.BooleanGuardPrune
import MicroCFTA.SourceSubstitutionPrecedence
import MicroCFTA.RecipeCompile

/-!
# Current guard decisions in recipe compilation

The current compiler classifies the precise runtime evaluator result. Its
diagnostic probes cannot turn an Unknown result into successful filtering.
Exact verdict transport here requires an unambiguous table. This is an
explicit proof premise, not a current compiler precheck. Logical safety for
accepted ambiguous cells is proved in `CurrentGuardLogicalPrune`.
-/
namespace MicroCFTA.BooleanGuardCompile
open FullSyntax SourceFormula SourceGuards SourceObservations

/-- Source guard classification with the current public sparse evaluator. -/
def decision (solver : Entailment Formula) (guard : Guard Formula) (cell : Observations Formula)
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool) : Except RecipeCompile.Error Bool :=
  RecipeCompile.constraintDecision
    (SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver cell guard)
    semantic allYes allNo mixedLeaf equalities same

/-- Only Yes or No can produce a successful compiler filter decision. -/
theorem classification (actual semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same answer : Bool)
    (success : RecipeCompile.constraintDecision actual semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    actual = (if answer then .yes else .no) := by
  cases answer
  · exact (RecipeCompile.constraintDecision_reject _ _ _ _ _ _ _).mp success
  · exact (RecipeCompile.constraintDecision_accept _ _ _ _ _ _ _).mp success

/-- Successful source filtering retains exactly the confirmed terms in each observation cell. -/
theorem decision_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (unambiguous : ambiguous cell (sameShape operations cell []) guard = [])
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    SourceSubstitutionPrecedence.evaluateGuard operations solver guard term = (if answer then .yes else .no) := by
  have classified := classification _ semantic allYes allNo mixedLeaf equalities same answer success
  have current := SourceSubstitutionPrecedence.public_known operations solver cell (sameShape operations cell) true guard unambiguous
  change SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver cell guard =
    SourceBooleanEntry.evaluateGuardWithShape operations solver cell guard at current
  rw [current] at classified
  have decided : SourceBooleanEntry.evaluateGuardWithShape operations solver cell guard ≠ .unknown := by
    rw [classified]
    cases answer <;> decide
  rw [SourceSubstitutionPrecedence.complete_unchanged]
  exact (SourceBooleanBridge.complete_decision model nullary laws sortDomain solver stable guard cell term reads
    unambiguous decided).symm.trans classified

/-- Boolean retention and complete confirmed membership agree after successful classification. -/
theorem retain_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (unambiguous : ambiguous cell (sameShape operations cell []) guard = [])
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    answer = true ↔ SourceSubstitutionPrecedence.evaluateGuard operations solver guard term = .yes := by
  rw [decision_exact model nullary laws sortDomain solver stable guard cell term reads unambiguous
    semantic allYes allNo mixedLeaf equalities same answer success]
  cases answer <;> simp

/-- No diagnostic probes can turn the repaired same-scope Unknown into a successful filter. -/
theorem same_scope_compiler_no_success (semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same answer : Bool) :
    decision NestedScopeCapture.solver SameScopeIdentityCapture.guard (observe NestedScopeCapture.term)
      semantic allYes allNo mixedLeaf equalities same ≠ .ok answer := by
  unfold decision
  rw [SourceSubstitutionPrecedence.same_scope_unknown]
  exact RecipeCompile.constraintDecision_unknown semantic allYes allNo mixedLeaf equalities same answer

/-- Semantic Unknown sends the repaired same-scope witness to the source solver error. -/
theorem same_scope_compiler_unknown (allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool) :
    decision NestedScopeCapture.solver SameScopeIdentityCapture.guard (observe NestedScopeCapture.term)
      .unknown allYes allNo mixedLeaf equalities same = .error .solverUnknown := by
  simp [decision, SourceSubstitutionPrecedence.same_scope_unknown, RecipeCompile.constraintDecision]

end MicroCFTA.BooleanGuardCompile
