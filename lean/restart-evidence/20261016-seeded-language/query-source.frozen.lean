import MicroCFTA.SourceCurrentAllocatedSeededLanguage
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentConjunctionClassWitness

/-!
# Current checked class-query refutation

The actual false secondary gate supplies selected-path support. The checked
seeded fold constructs its own input inventories and language receipt.
A satisfied active class therefore gives the actual query a common proper
subtree. A true current conjunction memo answer excludes that subtree.
Unselected original siblings can remain open.
-/
namespace MicroCFTA.SourceCurrentConjunctionRefusedClassQuery
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedSeededQuery (Seeded SeededRanges)
open SourceCurrentAllocatedSeededLanguage (Receipt)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable {width : Nat}

/-- The actual checked query retains a common subtree that is strictly smaller than the parent. -/
theorem class_witness [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {before after : Checked width} {anchor : State Symbol Guard} {query : Value Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (actual : Seeded values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query after)
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)
    (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ next, Receipt formulas solver next before query after ∧
      ∃ part, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query part ∧
        part.height < (Term.node symbol terms).height := by
  have proper := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  obtain ⟨next, receipt, included⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
    formulas solver inventory unconstrained paths values gate actual ready.good
      (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
      ready.scopedCache ready.idle admitted available proper ranges
  obtain ⟨part, common, smaller⟩ :=
    SourceCurrentConjunctionClassWitness.class_signed_common (.node symbol terms) paths active satisfied
  exact ⟨next, receipt, part,
    included (SourceCurrentConjunctionClassWitness.class_nonempty paths active) ambient symbol terms part accepted common,
    smaller⟩

/-- A true current memo hit or actual miss refutes the original class at its checked query. -/
theorem refutes_current_memo [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {before middle : Checked width} {anchor : State Symbol Guard} {query : Value Symbol Guard}
    {budget : Nat} {memo saved : Memo} {after : Physical}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (actual : Seeded values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query middle)
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor))
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  intro satisfied
  obtain ⟨_, receipt, part, acceptedPart, _⟩ := class_witness formulas solver inventory unconstrained paths active values
    gate actual ranges ready admitted available ambient symbol terms accepted satisfied
  have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps memo correct
  have checked := SourceCurrentConjunctionMemo.verified formulas solver call receipt.effects.ready receipt.available queryCorrect
  exact checked.2.2.1.2 rfl ambient part acceptedPart

end MicroCFTA.SourceCurrentConjunctionRefusedClassQuery
