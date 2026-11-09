import MicroCFTA.SourceCurrentConjunctionSharedWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorklistSemantics
import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationSoundness
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStoredDomain
import MicroCFTA.SourceCurrentConjunctionWorklistSoundness

/-!
# Conservative answers from actual shared decisions

The actual exploration derives coupled descriptor origins and raw sources.
The same cached table read derives semantic coverage and its physical
domain. The actual fixed-point answer then excludes accepted finite terms
when it returns true. Open queries return false. This result does not claim
Boolean completeness, memo correctness, or selected-caller adoption.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerSoundness
open Language
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorker (decision Outcome endpointCredits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
local notation "explore" => SourceCurrentConjunctionSharedWorklistRun.explore
local notation "readTable" => SourceCurrentConjunctionSharedWorklistMaterialization.readTable
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A true actual shared decision excludes every accepted finite term at the original query. -/
theorem decision_sound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    {p h budget : Nat} {query : Node} {before : Physical} {after : WorkState} {answer : Bool}
    (actual : decision p h budget query before = .done answer after)
    (ready : Ready before) (available : Available before.heap query) :
    answer = true → ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  intro verdict
  cases classified : closed query with
  | false =>
      rw [SourceCurrentConjunctionSharedWorker.decision_open p h budget query before classified] at actual
      cases actual
      cases verdict
  | true =>
      simp only [decision, classified, ite_true] at actual
      cases advanced : explore p h budget query before with
      | failed fault final =>
          simp only [advanced] at actual
          cases actual
      | done event final =>
          cases read : readTable (endpointCredits p h budget query before) final with
          | none =>
              simp only [advanced, read] at actual
              cases actual
          | some table =>
              cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
                  (table.length + 1) (fun _ => false) with
              | none =>
                  simp only [advanced, read, grown] at actual
                  cases actual
              | some known =>
                  simp only [advanced, read, grown] at actual
                  have checked := Outcome.done.inj actual
                  have answerTrue : SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known query = true :=
                    checked.1.trans verdict
                  have values := SourceCurrentConjunctionSharedWorklistValues.explore_values p h budget query before ready available
                  have reached : Effects before final.storage.requirements.physical ∧
                      SourceCurrentConjunctionSharedWorklistValues.Invariant final := by
                    simpa only [advanced, SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using values
                  have finalClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant final := by
                    simpa only [advanced, SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using
                      SourceCurrentConjunctionSharedWorklistClosed.explore_closed p h budget query before ready available
                  have noEmpty : SourceCurrentConjunctionSharedWorklistStoredDomain.NoEmptyTable final := by
                    simpa only [advanced, SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using
                      SourceCurrentConjunctionSharedWorklistStoredDomain.explore_noEmpty p h budget query before
                  have sources := SourceCurrentConjunctionSharedWorklistSemantics.explore_sources
                    formulas solver ambient p h budget query before ready available
                  rw [advanced] at sources
                  obtain ⟨origins, raw, current⟩ := sources
                  have coverage := SourceCurrentConjunctionSharedWorklistMaterializationSoundness.readTable_covered
                    (SourceEqualityPCSGuard.holds formulas solver) ambient
                    (endpointCredits p h budget query before) final table origins raw read current
                  have domain := SourceCurrentConjunctionSharedWorklistStoredDomain.readTable_domain
                    (endpointCredits p h budget query before) final table read reached.2 finalClosed noEmpty
                  exact SourceCurrentConjunctionTableSoundness.answer_sound .empty key closed
                    (Available final.storage.requirements.physical.heap) table domain
                    (SourceCurrentConjunctionWorklistSoundness.key_faithful
                      final.storage.requirements.physical.heap reached.1.ready.semantic)
                    (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                    (InternedGuardedLanguage.laws (SourceEqualityPCSGuard.holds formulas solver) ambient).empty
                    coverage query (reached.1.keeps.available query available) (table.length + 1) known grown answerTrue

/-- Every actual successful shared decision has the complete conservative memo-answer law. -/
theorem decision_answer_sound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {p h budget : Nat} {query : Node} {before : Physical} {after : WorkState} {answer : Bool}
    (actual : decision p h budget query before = .done answer after)
    (ready : Ready before) (available : Available before.heap query) :
    SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer := by
  constructor
  · intro notClosed
    have openInput : closed query = false := by
      cases classified : closed query with
      | false => rfl
      | true => exact False.elim (notClosed (List.isEmpty_iff.mp classified))
    have skipped := SourceCurrentConjunctionSharedWorker.decision_open p h budget query before openInput
    exact (Outcome.done.inj (skipped.symm.trans actual)).1.symm
  · intro verdict ambient
    exact decision_sound formulas solver ambient actual ready available verdict

end MicroCFTA.SourceCurrentConjunctionSharedWorkerSoundness
