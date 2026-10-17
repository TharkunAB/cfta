import MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace GeneratedReviewIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room advance)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits Frame)
open SourceCurrentConstrainedCapGeneratedQuerySequence (Pool Run)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {bits depth : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem three_meaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (memos : EndpointMemoGateTrace.Memos)
    (profile : Profile) (left right : Value Symbol Guard)
    (before after : Checked (bits + 2)) (results : List (Value Symbol Guard))
    (actual : Run depth formulas solver memos profile [(0, 1), (2, 0), (3, 1)]
      [left, right] before results after) :
    ∃ first second third, results = [first, second, third] ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient third term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term := by
  cases actual with
  | cons leftFound rightFound firstReceipt tail =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at leftFound rightFound
    cases leftFound
    cases rightFound
    cases tail with
    | cons leftFound rightFound secondReceipt tail =>
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at leftFound rightFound
      cases leftFound
      cases rightFound
      cases tail with
      | cons leftFound rightFound thirdReceipt tail =>
        simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.some.injEq] at leftFound rightFound
        cases leftFound
        cases rightFound
        cases tail with
        | nil =>
          refine ⟨_, _, _, rfl, ?_⟩
          intro ambient term
          rw [thirdReceipt.query.meaning ambient term, secondReceipt.query.meaning ambient term,
            firstReceipt.query.meaning ambient term]
          constructor
          · intro both
            exact ⟨both.1.1.1, both.2⟩
          · intro both
            exact ⟨⟨both, both.1⟩, both.2⟩

/-- One initial reservation constructs three exact result-fed queries and their final language. -/
theorem three_result_fed (profile : Profile) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2))
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (left right : Value Symbol Guard) (known : Pool depth [left, right] before)
    (room : Room bits (advance profile 2))
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ first second third after next,
      Run depth formulas solver memos profile [(0, 1), (2, 0), (3, 1)]
        [left, right] before [first, second, third] after ∧
      Frame formulas solver next after ∧ Fits (advance profile 3) after ∧
      SourceRecursiveIntersectionThunks.Extension before.native.machine after.native.machine ∧
      Pool depth ([left, right] ++ [first, second, third]) after ∧
      EndpointMemoGateTrace.Valid after.native.machine.heap memos ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient third term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term := by
  have supported : SourceCurrentConstrainedCapGeneratedQuerySequence.Supported
      [left, right].length [(0, 1), (2, 0), (3, 1)] := by decide
  have reserved := (SourceCurrentAllocatedNativeResourceForecast.reserved_iff_last bits profile 2).mpr room
  obtain ⟨results, after, next, actual, finalFrame, finalFits, extension, pool, globals, _count⟩ :=
    SourceCurrentConstrainedCapGeneratedQuerySequence.complete_many profile depth formulas solver
      [(0, 1), (2, 0), (3, 1)] [left, right] supported reserved inventory before frame fits known memos valid
  obtain ⟨first, second, third, equal, language⟩ :=
    three_meaning formulas solver memos profile left right before after results actual
  subst results
  exact ⟨first, second, third, after, next, actual, finalFrame, finalFits, extension, pool, globals, language⟩

end GeneratedReviewIntegration

#print axioms GeneratedReviewIntegration.three_result_fed
#check @GeneratedReviewIntegration.three_result_fed
