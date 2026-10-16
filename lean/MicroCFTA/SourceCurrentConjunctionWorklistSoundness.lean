import MicroCFTA.SourceCurrentConjunctionWorklist
import MicroCFTA.SourceCurrentConjunctionRowsSoundness
import MicroCFTA.SourceCurrentConjunctionTableSoundness

/-!
# Sound actual current conjunction exploration

Each reached admission derives its row coverage from actual physical reads,
equality allocation, and requirement projections. The induction retains one
immutable language meaning and the exact returned physical states.
The final table needs no supplied row function or final coverage oracle.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorklistSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionWorklist
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- Actual final table readiness supplies the scoped stored-domain record. -/
theorem stored_domain {state : Physical} {table : List Entry} (stored : TableReady state table) :
    SourceCurrentConjunctionTableSoundness.StoredDomain .empty closed (Available state.heap) table := by
  intro entry member
  have own := stored entry member
  refine ⟨?_, ?_, own.1, ?_⟩
  · apply List.all_eq_true.mpr
    intro value included
    exact List.isEmpty_iff.mpr (own.2.1 value included)
  · intro impossible
    have empty := (SourceCurrentConjunctionRequirements.any_empty entry.nodes).mpr impossible
    rw [own.2.2.1] at empty
    cases empty
  · intro row rowIn nodes nodesIn value valueIn
    exact (own.2.2.2 row rowIn nodes nodesIn).1 value valueIn

private theorem source_key (value : Value Symbol Guard) (closed : value.free = []) (nonempty : value ≠ .empty) :
    SourceEmptinessKeys.key value = some (SourceCurrentConjunctionRequirements.key value) := by
  obtain ⟨entry, field⟩ := SourceEmptinessKeys.entry_of_closed value closed nonempty
  have raw := SourceEmptinessKeys.rawKey_of_entry value entry field
  simp only [SourceEmptinessKeys.key, raw, Option.map_some, SourceCurrentConjunctionRequirements.key, Option.getD_some]

/-- Complete closed resident records derive scoped identity faithfulness at the actual heap. -/
theorem key_faithful (heap : State Symbol Guard) (semantic : SemanticReady heap) :
    SourceCurrentConjunctionTableSoundness.KeyFaithful .empty key closed (Available heap) := by
  intro left right leftAvailable rightAvailable leftNonempty rightNonempty leftClosed rightClosed same
  have firstClosed : left.free = [] := List.isEmpty_iff.mp leftClosed
  have secondClosed : right.free = [] := List.isEmpty_iff.mp rightClosed
  exact SourceEmptinessKeys.key_injective heap semantic.ready.semantic.1.normal.facts.coherent
    left right leftAvailable rightAvailable firstClosed secondClosed
    ((source_key left firstClosed leftNonempty).trans
      ((congrArg some same).trans (source_key right secondClosed rightNonempty).symm))

end MicroCFTA.SourceCurrentConjunctionWorklistSoundness

namespace MicroCFTA.SourceCurrentConjunctionWorklist
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTableSoundness (Covered)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- Actual worklist observations derive final readiness and each stored row's language receipt. -/
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
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified rows ready inputs noFree
      have coverage := SourceCurrentConjunctionRowsSoundness.rows_coverage rows ready inputs noFree formulas solver ambient
      have nextTable : TableReady middle (⟨nodes, requirements⟩ :: table) := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨fun value included => own.1.keeps.available value (inputs value included), noFree, nonempty, own.2⟩
        · exact table_keeps own.1.keeps stored entry member
      have nextPending : PendingReady middle (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      have nextCovered : Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
          (⟨nodes, requirements⟩ :: table) := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact coverage
        · exact covered entry member
      have later := ih own.1.ready nextTable nextPending nextCovered
      exact ⟨own.1.trans later.1, later.2⟩

end MicroCFTA.SourceCurrentConjunctionWorklist

namespace MicroCFTA.SourceCurrentConjunctionWorklistSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache
open SourceCurrentConjunctionWorklist
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTableSoundness (Covered)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- A reached finite-table true verdict is sound at the actual final heap. -/
theorem table_sound [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) {after : Physical} {final : List Entry}
    (ready : Ready after) (stored : TableReady after final)
    (covered : Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) final)
    (query : List (Value Symbol Guard)) (available : Values after.heap query)
    (verdict : SourceCurrentConjunctionEmptinessTable.provablyEmpty .empty key closed final query = true) :
    ∀ term, ¬SourceCurrentConjunctionEmptinessRows.Accepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) query term := by
  classical
  exact SourceCurrentConjunctionTableSoundness.provablyEmpty_sound .empty key closed (Available after.heap) final
    (stored_domain stored) (key_faithful after.heap ready.semantic)
    (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
    (fun term => (InternedGuardedLanguage.laws _ ambient).empty term) covered query available verdict

/-- Empty-start actual exploration derives its stored-domain and conservative Boolean law. -/
theorem entered_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (budget : Nat) (pending : List (List (Value Symbol Guard)))
    (before : Physical) (ready : Ready before) (available : PendingReady before pending) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧ TableReady after final ∧
      Covered (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) final ∧
      SourceCurrentConjunctionTableSoundness.StoredDomain .empty closed (Available after.heap) final ∧
      final.length ≤ budget ∧
      ∀ query, Values after.heap query →
        SourceCurrentConjunctionEmptinessTable.provablyEmpty .empty key closed final query = true →
        ∀ term, ¬SourceCurrentConjunctionEmptinessRows.Accepts
          (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) query term := by
  obtain ⟨final, after, actual, _, _, bound⟩ := entered budget pending before ready available
  have checked := actual.verified formulas solver ambient ready
    (by intro entry member; cases member) available (by intro entry member; cases member)
  exact ⟨final, after, actual, checked.1, checked.2.1, checked.2.2, stored_domain checked.2.1, bound,
    fun query available verdict => table_sound formulas solver ambient checked.1.ready checked.2.1 checked.2.2 query available verdict⟩

/-- The public closed guard and actual completed grow exclude a queried original language. -/
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
    (stored_domain checked.2.1) (key_faithful after.heap checked.1.ready.semantic)
    (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
    (fun term => (InternedGuardedLanguage.laws _ ambient).empty term) checked.2.2 start
    (checked.1.keeps.available start startAvailable) fuel known done verdict

end MicroCFTA.SourceCurrentConjunctionWorklistSoundness
