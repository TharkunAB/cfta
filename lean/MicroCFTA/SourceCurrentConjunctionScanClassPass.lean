import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

/-!
# One current checked Scan and its reached class continuation

A true current emptiness answer erases the original child slots. A
successful Scan runs the literal required worker and the checked class
right fold. Both branches retain the same actual Scan and complete state.
Range plans inspect only actual reached execution prefixes.
-/
namespace MicroCFTA.SourceCurrentConjunctionScanClassPass
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Raw reduction records one Scan and only the continuation selected by its result. -/
inductive Reduction (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Option Class → List (Value Symbol Guard) → Checked width → Fourth → Memo → Prop where
  | stopped {paths selected after saved}
      (scan : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
        before fourth (some paths) selected after saved) :
      Reduction budget records values before fourth memo (some paths)
        (EqualityLeafProjectionRuntimeEmpty.erase values) after saved memo
  | completed {selected middle savedFourth kept requiredValues heap results after saved}
      (scan : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
        before fourth none selected middle savedFourth)
      (retained : Retained scan records kept) {fuel readFuel : Nat}
      (required : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values middle.native.machine.heap = .done requiredValues heap)
      (pass : SourceCurrentAllocatedClassPass.Pass kept requiredValues (advanceHeap middle heap) memo results after saved) :
      Reduction budget records values before fourth memo none results after savedFourth saved

/-- Exact stage receipts pass each actual returned global bundle to the next stage. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {records : List SourceEqualityClassOrder.Record} →
    {values results : List (Value Symbol Guard)} → {before after : Checked width} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} → {outcome : Option Class} →
    Reduction budget records values before fourth memo outcome results after savedFourth saved → Memos → Memos → Prop where
  | stopped {budget : Nat} {records : List SourceEqualityClassOrder.Record}
      {values : List (Value Symbol Guard)} {before after : Checked width} {fourth saved : Fourth}
      {memo : Memo} {paths : Class} {selected : Constraints}
      {scan : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
        before fourth (some paths) selected after saved} {memos final : Memos}
      (reads : SourceCurrentConjunctionClassScanGlobalMemos.ScanReads scan memos final) :
      Reads formulas solver (Reduction.stopped (memo := memo) scan) memos final
  | completed {budget : Nat} {records kept : List SourceEqualityClassOrder.Record}
      {values requiredValues results : List (Value Symbol Guard)} {before middle after : Checked width}
      {fourth savedFourth : Fourth} {memo saved : Memo} {selected : Constraints} {heap : Heap}
      {scan : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
        before fourth none selected middle savedFourth}
      {retained : Retained scan records kept} {fuel readFuel : Nat}
      {required : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values middle.native.machine.heap = .done requiredValues heap}
      {pass : SourceCurrentAllocatedClassPass.Pass kept requiredValues (advanceHeap middle heap) memo results after saved}
      {memos scanMemos requiredMemos final : Memos}
      (first : SourceCurrentConjunctionClassScanGlobalMemos.ScanReads scan memos scanMemos)
      (second : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values requiredValues middle.native.machine.heap heap scanMemos requiredMemos)
      (last : SourceCurrentAllocatedClassPass.PassReads formulas solver pass requiredMemos final) :
      Reads formulas solver (Reduction.completed scan retained required pass) memos final

/-- Only successful actual Scan and required-worker prefixes demand class range checks. -/
structure Ranges (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) : Prop where
  scan : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values
    (records.map SourceEqualityClassOrder.Record.paths) before fourth
  pass : ∀ {selected middle savedFourth}
    (actual : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth none selected middle savedFourth),
    ∀ kept, Retained actual records kept → ∀ fuel readFuel requiredValues heap,
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values middle.native.machine.heap = .done requiredValues heap →
      SourceCurrentAllocatedClassPass.Ranges kept requiredValues (advanceHeap middle heap) memo

/-- Both source outcomes retain readiness, tables, arity, and independent original language bounds. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (records : List SourceEqualityClassOrder.Record) (values results : List (Value Symbol Guard))
    (before after : Checked width) (fourth savedFourth : Fourth) (memo saved : Memo)
    (outcome : Option Class) (final : Memos) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  originals : Values after.native.machine.heap values
  available : Values after.native.machine.heap results
  length : results.length = values.length
  stored : SourceCurrentMemoMergeEffects.Stored after.native.machine.heap saved
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  retained : Extends memo saved
  globals : Valid after.native.machine.heap final
  correct : SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap savedFourth
  fourthRetained : SourceCurrentEmptinessMemo.Extends fourth savedFourth
  rejected : ∀ paths, outcome = some paths → paths ∈ records.map SourceEqualityClassOrder.Record.paths ∧
    ∀ ambient symbol terms, All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
      ¬ClassSat (.node symbol terms) paths
  language : ∀ ambient symbol terms,
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    ((∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem erased_narrows (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) (EqualityLeafProjectionRuntimeEmpty.erase values) terms →
      All₂ (meaning holds ambient) values terms := by
  cases values with
  | nil => exact id
  | cons value values =>
      intro accepted
      cases accepted with
      | cons impossible _ => simp only [meaning] at impossible

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
private theorem required_length (fuel readFuel : Nat) (paths : List SourceEqualityNeeded.Path)
    (values results : List (Value Symbol Guard)) (before after : Heap)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after) :
    results.length = values.length := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at actual
      exact actual.length

/-- One actual current Scan constructs exactly its stopped or successful continuation. -/
theorem from_scan
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    {outcome : Option Class} {selected : Constraints} {middle : Checked width} {savedFourth : Fourth}
    (actualScan : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth outcome selected middle savedFourth)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget records values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Reduction budget records values before fourth memo outcome results after savedFourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  obtain ⟨scanMemos, scanInventory, scanReads, scanValid, scanReady, scanAdmitted,
      scanEffects, scanValues, scanCorrect, fourthRetained, sound⟩ :=
    SourceCurrentConjunctionClassScanGlobalMemos.verified formulas solver inventory actualScan ready admitted available
      pathsProper pathsActive correct ranges.scan memos valid
  cases outcome with
  | some paths =>
      have original : paths ∈ records.map SourceEqualityClassOrder.Record.paths :=
        SourceCurrentConjunctionClassScan.stopped_member actualScan
      refine ⟨EqualityLeafProjectionRuntimeEmpty.erase values, middle, memo, scanInventory, scanMemos,
        .stopped actualScan, .stopped scanReads,
        scanReady, scanAdmitted, scanEffects, scanValues,
        (SourceEqualityEmptyPropagation.erased_scope middle.native.machine.heap values).1,
        List.length_map _, stored.grows scanEffects.keeps, covered, extends_refl _, scanValid,
        scanCorrect, fourthRetained, ?_, ?_⟩
      · intro stopped same
        have same := Option.some.inj same
        subst stopped
        exact ⟨original, sound paths rfl⟩
      · intro ambient symbol terms
        have narrows := erased_narrows (SourceEqualityPCSGuard.holds formulas solver) ambient values terms
        refine ⟨narrows, fun satisfied => ⟨narrows, ?_⟩⟩
        intro accepted
        obtain ⟨record, present, same⟩ := List.mem_map.mp original
        exact False.elim (sound paths rfl ambient symbol terms accepted (same ▸ satisfied record present))
  | none =>
      obtain ⟨kept, firstMemos, requiredMemos, requiredInventory, requiredValues, heap, retained, sublist, selectedEq,
          keptFields, firstReads, required, requiredReads, requiredValid, _⟩ :=
        SourceCurrentConjunctionRequiredGlobalMemos.records_required_memos formulas solver inventory records actualScan
          ready admitted available proper fields correct ranges.scan memos valid
      obtain ⟨fuel, readFuel, enough⟩ := required.stable
      have requiredDone := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
      have passRanges := ranges.pass actualScan kept retained fuel readFuel requiredValues heap requiredDone
      obtain ⟨results, after, saved, next, final, passActual, passReads, checked⟩ :=
        SourceCurrentConjunctionRequiredClassPass.finite formulas solver requiredInventory required kept selectedEq
          (fun record member => (keptFields record member).1)
          (fun record member => (keptFields record member).2.2) memo
          (stored.grows scanEffects.keeps) covered passRanges requiredMemos requiredValid
      refine ⟨results, after, saved, next, final,
        .completed actualScan retained requiredDone passActual,
        .completed (retained := retained) (required := requiredDone) firstReads requiredReads passReads,
        checked.pass.ready, checked.pass.admitted, scanEffects.trans checked.effects, checked.originals_available,
        checked.pass.available, checked.pass.transport.length_eq.symm.trans (required_length _ _ _ _ _ _ _ requiredDone),
        checked.pass.stored, checked.pass.covered, checked.pass.retained, checked.pass.globals.valid,
        checked.fourth_correct savedFourth scanCorrect, fourthRetained, ?_, ?_⟩
      · intro paths impossible
        cases impossible
      · intro ambient symbol terms
        have language := checked.language ambient symbol terms
        refine ⟨fun accepted => (language.1 accepted).1, ?_⟩
        intro satisfied
        apply language.2
        intro paths member
        rw [← selectedEq] at member
        obtain ⟨record, present, same⟩ := List.mem_map.mp member
        exact same ▸ satisfied record (sublist.subset present)

/-- Reached range plans construct one current Scan and its complete actual local reduction. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget records values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ outcome results after savedFourth saved next final,
      ∃ actual : Reduction budget records values before fourth memo outcome results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  obtain ⟨outcome, selected, middle, savedFourth, scan, _⟩ := SourceCurrentConjunctionClassScanCompletion.finite
    formulas solver budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth ready available pathsProper correct ranges.scan
  obtain ⟨results, after, saved, next, final, actual, reads, receipt⟩ := from_scan formulas solver inventory budget
    records values before fourth memo scan ready admitted available proper fields correct stored covered ranges memos valid
  exact ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt⟩

end MicroCFTA.SourceCurrentConjunctionScanClassPass
