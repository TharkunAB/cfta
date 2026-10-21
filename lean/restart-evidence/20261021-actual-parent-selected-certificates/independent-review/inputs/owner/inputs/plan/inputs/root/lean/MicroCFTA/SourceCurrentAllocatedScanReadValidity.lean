import MicroCFTA.SourceCurrentAllocatedQueryReadValidity
import MicroCFTA.SourceCurrentAllocatedScanSourceReads
import MicroCFTA.SourceCurrentAllocatedPrimaryCompletion

/-!
# Validity of the supplied current source-aligned Scan reads

Every visited primary call uses the exact source node. Secondary, seeded,
and conjunction phases retain their actual final tables. The proof follows
the supplied schedule and derives physical and fourth-memo receipts.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanReadValidity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
open SourceCurrentConjunctionQueryGlobalMemos (query_memos)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Actual source-aligned reads derive their own final validity and all physical Scan receipts. -/
theorem scan
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    {actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved}
    {memos final : Memos} (reads : ScanReads actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.native.machine.heap final ∧ Ready after ∧ Effects (physical before) (physical after) ∧
      Values after.native.machine.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  revert ready available proper correct ranges valid
  induction reads with
  | nil =>
      intro ready available proper correct ranges valid
      exact ⟨valid, ready, .refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),
        available, correct, fun _ _ found => found⟩
  | selected firstRead tailRead ih =>
      intro ready available proper correct ranges valid
      have first := primary_effects unconstrained reaches (by assumption) ready available
      have firstKept := SourceCurrentAllocatedGateReadValidity.primary_class firstRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      obtain ⟨finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCorrect (ranges.1 _ (by assumption)) firstKept.valid
      exact ⟨finalValid, finalReady, first.2.1.trans effects, finalValues, finalCorrect, retained⟩
  | skipped firstRead secondRead tailRead ih =>
      intro ready available proper correct ranges valid
      have first := primary_effects unconstrained reaches (by assumption) ready available
      have firstKept := SourceCurrentAllocatedGateReadValidity.primary_class firstRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      have second := secondary_effects unconstrained (by assumption) first.1 first.2.2
      have secondKept := SourceCurrentAllocatedGateReadValidity.secondary_class secondRead
        (SourceCurrentClassGateCompletion.gate_ready first.1.semantic first.1.costs) first.2.2 firstKept.valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver (first.2.1.trans second.2.1).keeps _ correct
      obtain ⟨finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih second.1 second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCorrect (ranges.2.1 _ (by assumption) _ (by assumption)) secondKept.valid
      exact ⟨finalValid, finalReady, first.2.1.trans (second.2.1.trans effects), finalValues, finalCorrect, retained⟩
  | continued firstRead queryRead tailRead ih =>
      intro ready available proper correct ranges valid
      have first := primary_effects unconstrained reaches (by assumption) ready available
      have firstKept := SourceCurrentAllocatedGateReadValidity.primary_class firstRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      have reached := ranges.2.2 _ (by assumption) _ (by assumption)
      obtain ⟨queryValid, queryReady, queryEffects, queryValues, queryCorrect, queryRetained⟩ :=
        SourceCurrentAllocatedQueryReadValidity.query queryRead (proper _ List.mem_cons_self) reached.1
          first.1 first.2.2 formulas solver firstCorrect firstKept.valid
      obtain ⟨finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih queryReady queryValues (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          queryCorrect (reached.2 _ _ (by assumption) _ _ (by assumption)) queryValid
      exact ⟨finalValid, finalReady, first.2.1.trans (queryEffects.trans effects), finalValues, finalCorrect,
        fun key entry found => retained key entry (queryRetained key entry found)⟩
  | stopped firstRead queryRead =>
      intro ready available proper correct ranges valid
      have first := primary_effects unconstrained reaches (by assumption) ready available
      have firstKept := SourceCurrentAllocatedGateReadValidity.primary_class firstRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      have reached := ranges.2.2 _ (by assumption) _ (by assumption)
      obtain ⟨finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        SourceCurrentAllocatedQueryReadValidity.query queryRead (proper _ List.mem_cons_self) reached.1
          first.1 first.2.2 formulas solver firstCorrect firstKept.valid
      exact ⟨finalValid, finalReady, first.2.1.trans effects, finalValues, finalCorrect, retained⟩

/-- Every current checked Scan derives the global tables and all physical and fourth-memo invariants. -/
theorem construct
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
      obtain ⟨nextMemos, firstRead, firstKept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      obtain ⟨final, tailRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCorrect (ranges.1 _ primary) nextMemos firstKept.valid
      exact ⟨final, .selected firstRead tailRead, finalValid, finalReady, first.2.1.trans effects,
        finalValues, finalCorrect, retained⟩
  | skipped primary secondary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class _ _ _ _ _ primary
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
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class _ _ _ _ _ primary
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
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class _ _ _ _ _ primary
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct
      have reached := ranges.2.2 _ primary _ secondary
      obtain ⟨final, queryRead, finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
        query_memos _ values (proper _ List.mem_cons_self) secondary seeded call reached.1
          first.1 first.2.2 formulas solver firstCorrect primaryMemos primaryKept.valid
      exact ⟨final, .stopped primaryRead queryRead, finalValid, finalReady,
        first.2.1.trans effects, finalValues, finalCorrect, retained⟩

end MicroCFTA.SourceCurrentAllocatedScanReadValidity
