import MicroCFTA.SourceCurrentConjunctionRefusedClassQuery
open MicroCFTA MicroCFTA.Language MicroCFTA.EqualityNormalize
open MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedProbeProvenance
open MicroCFTA.InternedNestedProvenance (Values)
open MicroCFTA.SourceCurrentAllocatedNativeEffects (physical)
open MicroCFTA.SourceCurrentAllocatedNativeInventoryState (Inventory At)
open MicroCFTA.SourceCurrentAllocatedSeededQuery (Seeded SeededRanges)
open MicroCFTA.SourceCurrentConjunctionClassScan (Ready advanceHeap)
open MicroCFTA.InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (inventory : Inventory) (u : Value Symbol Guard → Bool) (paths : Class) (active : Nontrivial paths)
  (values : List (Value Symbol Guard)) {before middle : Checked width} {anchor : State Symbol Guard}
  {query : Value Symbol Guard} {budget : Nat} {memo : Memo}
  (gate : SourceCurrentSecondaryTrace.ClassTrace u values paths before.native.machine.heap false anchor)
  (seeded : Seeded values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query middle)
  (ranges : SeededRanges values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor))
  (ready : Ready before) (admitted : At formulas solver inventory before)
  (available : Values before.native.machine.heap values)
  (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
  (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
  (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)

-- An actual warm hit uses the stored original record; it does not rerun a Decision.
example (original : Value Symbol Guard) (found : memo query.referenceOf = some (original, true)) :
    ¬ClassSat (.node symbol terms) paths := by
  exact SourceCurrentConjunctionRefusedClassQuery.refutes_current_memo formulas solver inventory u paths active values
    gate seeded ranges (SourceCurrentConjunctionMemo.Call.hit (budget := budget) found)
    ready admitted available correct ambient symbol terms accepted

-- An actual miss uses the new conjunction Decision, with its literal saved memo.
example (absent : memo query.referenceOf = none) (after : Physical)
    (decision : SourceCurrentConjunctionDecision.Decision budget query (physical middle) true after) :
    ¬ClassSat (.node symbol terms) paths := by
  exact SourceCurrentConjunctionRefusedClassQuery.refutes_current_memo formulas solver inventory u paths active values
    gate seeded ranges (SourceCurrentConjunctionMemo.Call.miss absent decision)
    ready admitted available correct ambient symbol terms accepted
end
