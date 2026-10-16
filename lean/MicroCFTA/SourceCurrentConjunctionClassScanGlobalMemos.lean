import MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos
import MicroCFTA.SourceCurrentConjunctionClassScanSoundness

/-!
# Global gate tables through the current checked class Scan

Each reached primary, secondary, checked query, and current conjunction
memo call passes its actual returned tables to the next source operation.
A stopped class omits the suffix. Initial table validity and reached word
ranges derive final validity. The semantic endpoint also derives the final
input inventory and original-class refutation from its legitimate warm entry.
These completed receipts do not prove GHC forcing or memo publication.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
open SourceCurrentConjunctionQueryGlobalMemos
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable {width : Nat}

/-- Only reached calls carry their exact returned three-table bundle to the next branch. -/
inductive ScanReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {values : List (Value Symbol Guard)} → {classes selected : Constraints} →
    {outcome : Option Class} → {before after : Checked width} → {memo saved : Memo} →
    Scan budget unconstrained reaches values classes before memo outcome selected after saved → Memos → Memos → Prop where
  | nil : ScanReads .nil memos memos
  | selected (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (tail : ScanReads rest middle final) : ScanReads (.selected primary rest) memos final
  | skipped (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (second : SourceCurrentSecondaryMemos.ClassReads secondary middle later)
      (tail : ScanReads rest later final) : ScanReads (.skipped primary secondary rest) memos final
  | continued {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} {classes selected : Constraints}
      {before middle after : Checked width} {heap anchor : State Symbol Guard} {later : Physical}
      {query : Value Symbol Guard} {memo savedMemo saved : Memo} {outcome : Option Class}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later savedMemo}
      {rest : Scan budget unconstrained reaches values classes (advancePhysical middle later)
        savedMemo outcome selected after saved}
      {memos first second final : Memos}
      (primaryRead : EndpointMemoGateTrace.ClassReads primary memos first)
      (queryRead : QueryReads (before := advanceHeap before heap) secondary seeded call first second)
      (tailRead : ScanReads rest second final) :
      ScanReads (.continued primary secondary seeded call rest) memos final
  | stopped {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} {classes : Constraints}
      {before middle : Checked width} {heap anchor : State Symbol Guard} {later : Physical}
      {query : Value Symbol Guard} {memo saved : Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved}
      {memos first final : Memos}
      (primaryRead : EndpointMemoGateTrace.ClassReads primary memos first)
      (queryRead : QueryReads (before := advanceHeap before heap) secondary seeded call first final) :
      ScanReads (.stopped (classes := classes) primary secondary seeded call) memos final

/-- Every current checked Scan derives the global tables and all physical and fourth-memo invariants. -/
theorem scan_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    (trace : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, ScanReads trace memos final ∧ Valid after.native.machine.heap final ∧
      Ready after ∧ Effects (physical before) (physical after) ∧ Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  induction trace generalizing memos with
  | nil =>
      exact ⟨memos, .nil, valid, ready,
        .refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),
        available, correct, fun _ _ found => found⟩
  | selected primary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      obtain ⟨nextMemos, firstRead, firstKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      obtain ⟨final, tailRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCorrect (ranges.1 _ primary) nextMemos firstKept.valid
      exact ⟨final, .selected firstRead tailRead, finalValid, finalReady, first.2.1.trans effects,
        finalValues, finalCorrect, retained⟩
  | skipped primary secondary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      obtain ⟨nextMemos, secondaryRead, secondaryKept⟩ := SourceCurrentSecondaryMemos.lift_class _ _ _ _ _ secondary
        (SourceCurrentClassGateCompletion.gate_ready first.1.semantic first.1.costs) first.2.2 primaryMemos primaryKept.valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver
        (first.2.1.trans second.2.1).keeps _ correct
      obtain ⟨final, tailRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih second.1 second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCorrect (ranges.2.1 _ primary _ secondary) nextMemos secondaryKept.valid
      exact ⟨final, .skipped primaryRead secondaryRead tailRead, finalValid, finalReady,
        first.2.1.trans (second.2.1.trans effects), finalValues, finalCorrect, retained⟩
  | continued primary secondary seeded call rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      have reached := ranges.2.2 _ primary _ secondary
      obtain ⟨nextMemos, queryRead, queryValid, queryReady, queryEffects, queryValues, queryCorrect, queryRetained⟩ :=
        query_memos _ values (proper _ List.mem_cons_self) secondary seeded call reached.1
          first.1 first.2.2 formulas solver firstCorrect primaryMemos primaryKept.valid
      obtain ⟨final, tailRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih queryReady queryValues (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          queryCorrect (reached.2 _ _ seeded _ _ call) nextMemos queryValid
      exact ⟨final, .continued primaryRead queryRead tailRead, finalValid, finalReady,
        first.2.1.trans (queryEffects.trans effects), finalValues, finalCorrect,
        fun key entry found => retained key entry (queryRetained key entry found)⟩
  | stopped primary secondary seeded call =>
      have first := primary_effects unconstrained reaches primary ready available
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      have reached := ranges.2.2 _ primary _ secondary
      obtain ⟨final, queryRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        query_memos _ values (proper _ List.mem_cons_self) secondary seeded call reached.1
          first.1 first.2.2 formulas solver firstCorrect primaryMemos primaryKept.valid
      exact ⟨final, .stopped primaryRead queryRead, finalValid, finalReady,
        first.2.1.trans effects, finalValues, finalCorrect, retained⟩

/-- The same actual Scan derives global receipts, its final concrete input inventory, and sound rejection. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    (trace : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final next, ScanReads trace memos final ∧ Valid after.native.machine.heap final ∧ Ready after ∧
      At formulas solver next after ∧ Effects (physical before) (physical after) ∧
      Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      ∀ paths, outcome = some paths → ∀ ambient symbol terms,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        ¬ClassSat (.node symbol terms) paths := by
  obtain ⟨final, reads, finalValid, _⟩ := scan_memos trace ready available proper formulas solver correct ranges memos valid
  obtain ⟨next, finalReady, finalAdmission, effects, finalValues, finalCorrect, retained, sound⟩ :=
    SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory trace ready admitted available
      proper active correct ranges
  exact ⟨final, next, reads, finalValid, finalReady, finalAdmission, effects, finalValues, finalCorrect, retained, sound⟩

end MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos
