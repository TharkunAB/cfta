import MicroCFTA.SourceCurrentConjunctionRefusedClassQuery
import MicroCFTA.SourceCurrentConjunctionClassScanCompletion

/-!
# Sound stopped scans with changing checked input inventories

Actual gates retain the current inventory. Each reached checked seeded
query constructs its next inventory. The current conjunction memo retains
that inventory through its exact physical return. The induction follows
only the visited class prefix. A true answer refutes the named original
class for every accepted original forest. Reached word ranges remain explicit.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassScanSoundness
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan
open SourceCurrentConjunctionClassScanCompletion (Ranges)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- The reached scan derives its final inventory and soundness of every actual stop. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo) :
    ∃ next, Ready after ∧ At formulas solver next after ∧ Effects (physical before) (physical after) ∧
      Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      ∀ paths, outcome = some paths → ∀ ambient symbol terms,
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        ¬ClassSat (.node symbol terms) paths := by
  induction actual generalizing inventory with
  | nil =>
      refine ⟨inventory, ready, admitted,
        .refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),
        available, correct, (fun _ _ found => found), ?_⟩
      intro paths impossible
      cases impossible
  | @selected paths heap classes before memo outcome selected after saved primary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      obtain ⟨next, finalReady, finalAdmission, remaining, finalValues, finalCorrect, retained, sound⟩ :=
        ih inventory first.1 firstAdmission first.2.2
          (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) firstCorrect
          (ranges.1 heap primary)
      exact ⟨next, finalReady, finalAdmission, first.2.1.trans remaining, finalValues, finalCorrect, retained, sound⟩
  | @skipped paths heap anchor classes before memo outcome selected after saved primary secondary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      have secondAdmission := firstAdmission.advance ⟨anchor, (advanceHeap before heap).operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1)
      have secondCorrect := SourceCurrentEmptinessMemo.grows formulas solver second.2.1.keeps memo firstCorrect
      obtain ⟨next, finalReady, finalAdmission, remaining, finalValues, finalCorrect, retained, sound⟩ :=
        ih inventory second.1 secondAdmission second.2.2
          (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) secondCorrect
          (ranges.2.1 heap primary anchor secondary)
      exact ⟨next, finalReady, finalAdmission, first.2.1.trans (second.2.1.trans remaining),
        finalValues, finalCorrect, retained, sound⟩
  | @continued paths heap anchor before query middle memo later savedMemo classes outcome selected after saved
      primary secondary seeded decision rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have reached := ranges.2.2 heap primary anchor secondary
      obtain ⟨nextInventory, queryReceipt, _⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
        formulas solver inventory unconstrained paths values secondary seeded first.1.good first.2.1.ready
        first.1.scopedCache first.1.idle firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1
      have queryReady : Ready middle := ⟨queryReceipt.good, queryReceipt.effects.ready.semantic,
        queryReceipt.effects.ready.costs, queryReceipt.scopes, queryReceipt.idle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryReceipt.effects.keeps memo firstCorrect
      obtain ⟨memoReady, memoEffects, memoCorrect, _, memoRetained⟩ :=
        memo_effects formulas solver decision queryReady queryReceipt.available queryCorrect
      have memoAdmission := queryReceipt.admitted.advance later
        (SourceCurrentAllocatedQueryMemo.advance_extension middle later memoEffects)
      have memoValues : Values (advancePhysical middle later).native.machine.heap values := fun value member =>
        memoEffects.keeps.available value (queryReceipt.effects.keeps.available value (first.2.2 value member))
      obtain ⟨next, finalReady, finalAdmission, remaining, finalValues, finalCorrect, retained, sound⟩ :=
        ih nextInventory memoReady memoAdmission memoValues
          (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) memoCorrect
          (reached.2 query middle seeded later savedMemo decision)
      exact ⟨next, finalReady, finalAdmission,
        first.2.1.trans (queryReceipt.effects.trans (memoEffects.trans remaining)), finalValues, finalCorrect,
        (fun key entry found => retained key entry (memoRetained key entry found)), sound⟩
  | @stopped paths heap anchor before query middle memo later saved classes primary secondary seeded decision =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have reached := ranges.2.2 heap primary anchor secondary
      obtain ⟨next, queryReceipt, included⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
        formulas solver inventory unconstrained paths values secondary seeded first.1.good first.2.1.ready
        first.1.scopedCache first.1.idle firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1
      have queryReady : Ready middle := ⟨queryReceipt.good, queryReceipt.effects.ready.semantic,
        queryReceipt.effects.ready.costs, queryReceipt.scopes, queryReceipt.idle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryReceipt.effects.keeps memo firstCorrect
      obtain ⟨memoReady, memoEffects, memoCorrect, answer, retained⟩ :=
        memo_effects formulas solver decision queryReady queryReceipt.available queryCorrect
      have memoAdmission := queryReceipt.admitted.advance later
        (SourceCurrentAllocatedQueryMemo.advance_extension middle later memoEffects)
      refine ⟨next, memoReady, memoAdmission, first.2.1.trans (queryReceipt.effects.trans memoEffects),
        (fun value member => memoEffects.keeps.available value
          (queryReceipt.effects.keeps.available value (first.2.2 value member))), memoCorrect, retained, ?_⟩
      intro stopped same ambient symbol terms accepted satisfied
      have equal := Option.some.inj same
      subst stopped
      obtain ⟨part, common, _⟩ := SourceCurrentConjunctionClassWitness.class_signed_common
        (.node symbol terms) paths (active paths List.mem_cons_self) satisfied
      have acceptedPart := included
        (SourceCurrentConjunctionClassWitness.class_nonempty paths (active paths List.mem_cons_self))
        ambient symbol terms part accepted common
      exact answer.2 rfl ambient part acceptedPart

/-- An actual stopped scan refutes its named original class without a query-language premise. -/
theorem stopped_refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo (some paths) selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  obtain ⟨_, _, _, _, _, _, _, sound⟩ := verified formulas solver inventory actual ready admitted available proper active correct ranges
  exact sound paths rfl ambient symbol terms accepted

end MicroCFTA.SourceCurrentConjunctionClassScanSoundness
