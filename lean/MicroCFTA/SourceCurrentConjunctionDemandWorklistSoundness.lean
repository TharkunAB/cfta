import MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionWorklistSoundness
import MicroCFTA.SourceCurrentEmptinessMemo

/-!
# Conservative soundness of actual demand worklists

Zero and positive admissions derive coverage from the actual demand sample.
Their returned requirements retain the physical readiness needed by the
pending suffix. Overflow inserts no entry. A true final answer excludes
accepted terms. A false answer does not assert that a term exists.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (PendingReady TableReady closed closed_values table_keeps pending_keeps)
open SourceCurrentConjunctionTableSoundness (Covered)
open InternedGuardedLanguage (meaning)



section ActualMeaning
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- Actual tuple exploration derives final readiness and coverage for every stored entry. -/
theorem Run.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (ready : Ready before) (stored : TableReady before table) (available : PendingReady before pending)
    (covered : Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) table) :
    Effects before after ∧ TableReady after final ∧
      Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) final := by
  induction actual with
  | done => exact ⟨Effects.refl _ ready, stored, covered⟩
  | empty _ _ ih =>
      exact ih ready stored (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) covered
  | skip _ _ _ ih =>
      exact ih ready stored (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) covered
  | overflow _ fresh admission _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admission.effects ready inputs noFree
      have later := ih own.ready (table_keeps own.keeps stored)
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) covered
      exact ⟨own.trans later.1, later.2⟩
  | zero nonempty fresh admission _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admission.verified ready inputs noFree
      have coverage := admission.coverage ready inputs noFree formulas solver ambient
      have later := ih own.1.ready
        (by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨fun value included => own.1.keeps.available value (inputs value included), noFree, nonempty, by intro row absent; cases absent⟩
          · exact table_keeps own.1.keeps stored entry member)
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact coverage
          · exact covered entry member)
      exact ⟨own.1.trans later.1, later.2⟩
  | positive nonempty fresh admission _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admission.verified ready inputs noFree
      have coverage := admission.coverage ready inputs noFree formulas solver ambient
      have later := ih own.1.ready
        (by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨fun value included => own.1.keeps.available value (inputs value included), noFree, nonempty, own.2⟩
          · exact table_keeps own.1.keeps stored entry member)
        (by
          intro requirement member
          rcases List.mem_append.mp member with generated | earlier
          · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
            exact (own.2 row rowIn requirement requirementIn).1
          · exact pending_keeps own.1.keeps
              (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier)
        (by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact coverage
          · exact covered entry member)
      exact ⟨own.1.trans later.1, later.2⟩

/-- The actual grow result and a true answer exclude the queried language. -/
theorem run_answer_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (ready : Ready before) (stored : TableReady before table) (available : PendingReady before pending)
    (covered : Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) table)
    (start : Value Symbol Guard) (startAvailable : Available before.heap start)
    (fuel : Nat) (known : SourceCurrentConjunctionEmptinessTable.State key final → Bool)
    (done : SourceCurrentConjunctionEmptinessTable.grow .empty key closed final fuel (fun _ => false) = some known)
    (verdict : SourceCurrentConjunctionEmptinessTable.answer .empty key closed final known start = true) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient start term := by
  classical
  have checked := actual.verified formulas solver ambient ready stored available covered
  exact SourceCurrentConjunctionTableSoundness.answer_sound .empty key closed (Available after.heap) final
    (SourceCurrentConjunctionWorklistSoundness.stored_domain checked.2.1)
    (SourceCurrentConjunctionWorklistSoundness.key_faithful after.heap checked.1.ready.semantic)
    (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
    (fun term => (InternedGuardedLanguage.laws _ ambient).empty term) checked.2.2 start
    (checked.1.keeps.available start startAvailable) fuel known done verdict

/-- Actual decisions derive physical effects and conservative memo answers. -/
theorem Decision.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {result : Bool}
    (actual : Decision budget start before result after) (ready : Ready before)
    (available : Available before.heap start)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Effects before after ∧ SourceCurrentEmptinessMemo.AnswerSound formulas solver start result := by
  cases actual with
  | open_input _ =>
      exact ⟨Effects.refl _ ready, ⟨fun _ => rfl, by intro impossible; cases impossible⟩⟩
  | closed closedInput explored grown =>
      have pending : PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      have checked := explored.verified formulas solver (fun _ _ => False) ready
        (by intro entry member; cases member) pending (by intro entry member; cases member)
      refine ⟨checked.1, ?_, ?_⟩
      · intro notClosed
        exact False.elim (notClosed (List.isEmpty_iff.mp closedInput))
      · intro accepted ambient
        exact run_answer_sound formulas solver ambient explored ready
          (by intro entry member; cases member) pending (by intro entry member; cases member)
          start available _ _ grown accepted
end ActualMeaning
end MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
