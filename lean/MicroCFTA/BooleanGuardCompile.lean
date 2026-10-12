import MicroCFTA.BooleanGuardPrune
import MicroCFTA.RecipeCompile

/-!
# Current guard decisions in recipe compilation

The source compiler rejects ambiguity before querying the sparse entry. Its
diagnostic probes cannot turn an Unknown result into successful filtering.
Every successful group decision therefore agrees with each represented term.
-/
namespace MicroCFTA.BooleanGuardCompile
open FullSyntax SourceFormula SourceGuards SourceObservations

/-- Source guard classification with the current public sparse evaluator. -/
def decision (solver : Entailment Formula) (guard : Guard Formula) (cell : Observations Formula)
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool) : Except RecipeCompile.Error Bool :=
  RecipeCompile.constraintDecision (!(ambiguous cell (fun _ _ => none) guard).isEmpty)
    (SourceBooleanEntry.evaluateGuardWithShape operations solver cell guard)
    semantic allYes allNo mixedLeaf equalities same

/-- Only Yes or No can produce a successful compiler filter decision. -/
theorem classification (uncertain : Bool) (actual semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same answer : Bool)
    (success : RecipeCompile.constraintDecision uncertain actual semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    uncertain = false ∧ actual = (if answer then .yes else .no) := by
  cases uncertain
  · constructor
    · rfl
    · cases actual with
      | yes | no => simpa [RecipeCompile.constraintDecision] using success
      | unknown => exact False.elim (RecipeCompile.constraintDecision_unknown false semantic allYes allNo mixedLeaf equalities same answer success)
  · simp [RecipeCompile.constraintDecision] at success

/-- Successful source filtering retains exactly the confirmed terms in each observation cell. -/
theorem decision_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    SourceBooleanEntry.evaluateGuard operations solver guard term = (if answer then .yes else .no) := by
  have classified := classification _ _ semantic allYes allNo mixedLeaf equalities same answer success
  have gate : ambiguous cell (fun _ _ => none) guard = [] := by simpa using classified.1
  have decided : SourceBooleanEntry.evaluateGuardWithShape operations solver cell guard ≠ .unknown := by
    rw [classified.2]
    cases answer <;> decide
  exact (SourceBooleanBridge.complete_decision model nullary laws sortDomain solver stable guard cell term reads
    (FullGuardPruneStable.gate_unambiguous operations cell guard gate) decided).symm.trans classified.2

/-- Boolean retention and complete confirmed membership agree after successful classification. -/
theorem retain_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard Formula) (cell : Observations Formula) (term : Language.Term (Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (semantic allYes allNo : Guards.Verdict) (mixedLeaf equalities same answer : Bool)
    (success : decision solver guard cell semantic allYes allNo mixedLeaf equalities same = .ok answer) :
    answer = true ↔ SourceBooleanEntry.evaluateGuard operations solver guard term = .yes := by
  rw [decision_exact model nullary laws sortDomain solver stable guard cell term reads
    semantic allYes allNo mixedLeaf equalities same answer success]
  cases answer <;> simp

end MicroCFTA.BooleanGuardCompile
