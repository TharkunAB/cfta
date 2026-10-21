import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
import MicroCFTA.SourceCurrentAllocatedScanReadValidity
import MicroCFTA.SourceCurrentAllocatedScanSourceReads
import MicroCFTA.SourceCurrentConjunctionScanClassPass

/-!
# Receipts for an actual current Scan and class continuation

The supplied read graph fixes the returned global memo bundle. The actual
required return has a derived receipt. The actual class pass then derives
its receipt at its own returned checked state. No final invariant or
result-language premise is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionScanClassPassActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentConjunctionScanClassPass (Reduction Receipt)
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
      (reads : SourceCurrentAllocatedScanSourceReads.ScanReads scan memos final) :
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
      (first : SourceCurrentAllocatedScanSourceReads.ScanReads scan memos scanMemos)
      (second : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values requiredValues middle.native.machine.heap heap scanMemos requiredMemos)
      (last : SourceCurrentAllocatedClassPass.PassReads formulas solver pass requiredMemos final) :
      Reads formulas solver (Reduction.completed scan retained required pass) memos final


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
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after) :
    results.length = values.length := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at actual
      exact actual.length

/-- Source-refined reads retain the same historical continuation and returned bundle. -/
theorem Reads.erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class}
    {actual : Reduction budget records values before fourth memo outcome results after savedFourth saved}
    {memos final : Memos} (reads : Reads formulas solver actual memos final) :
    SourceCurrentConjunctionScanClassPass.Reads formulas solver actual memos final := by
  cases reads with
  | stopped first => exact .stopped first.erase
  | completed first second last =>
      exact .completed (retained := by assumption) (required := by assumption) first.erase second last

/-- Initial invariants derive the full receipt for the supplied actual continuation and reads. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  cases reads with
  | stopped scanRead =>
      rename_i paths selected scan
      obtain ⟨next, finalReady, finalAdmission, effects, finalValues, finalCorrect, retained, sound⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          pathsProper pathsActive correct ranges
      have coherent := (SourceCurrentAllocatedScanReadValidity.scan scanRead ready available pathsProper
        formulas solver correct ranges valid).1
      have original := SourceCurrentConjunctionClassScan.stopped_member scan
      refine ⟨next, finalReady, finalAdmission, effects, finalValues,
        (SourceEqualityEmptyPropagation.erased_scope _ values).1, List.length_map _,
        stored.grows effects.keeps, covered, extends_refl _, coherent, finalCorrect, retained, ?_, ?_⟩
      · intro stopped equality
        have same := Option.some.inj equality
        subst stopped
        exact ⟨original, sound paths rfl⟩
      · intro ambient symbol terms
        have narrows := erased_narrows (SourceEqualityPCSGuard.holds formulas solver) ambient values terms
        refine ⟨narrows, fun satisfied => ⟨narrows, ?_⟩⟩
        intro accepted
        obtain ⟨record, present, same⟩ := List.mem_map.mp original
        exact False.elim (sound paths rfl ambient symbol terms accepted (same ▸ satisfied record present))
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      obtain ⟨scanInventory, scanReady, scanAdmitted, scanEffects, scanValues, scanCorrect, fourthRetained, _⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          pathsProper pathsActive correct ranges
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
        formulas solver correct ranges valid).1
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
        scanReady.costs scanValues scanValid).1
      have retainedFields := retained.fields
      obtain ⟨next, checked⟩ := SourceCurrentConjunctionRequiredClassPass.verified formulas solver requiredInventory
        requiredReceipt kept retainedFields.2
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        last (stored.grows scanEffects.keeps) covered requiredValid
      refine ⟨next, checked.pass.ready, checked.pass.admitted, scanEffects.trans checked.effects,
        checked.originals_available, checked.pass.available,
        checked.pass.transport.length_eq.symm.trans (required_length _ _ _ _ _ _ _ required),
        checked.pass.stored, checked.pass.covered, checked.pass.retained, checked.pass.globals.valid,
        checked.fourth_correct _ scanCorrect, fourthRetained, ?_, ?_⟩
      · intro paths impossible
        cases impossible
      · intro ambient symbol terms
        have language := checked.language ambient symbol terms
        refine ⟨fun accepted => (language.1 accepted).1, ?_⟩
        intro satisfied
        apply language.2
        intro paths member
        rw [← retainedFields.2] at member
        obtain ⟨record, present, same⟩ := List.mem_map.mp member
        exact same ▸ satisfied record (retainedFields.1.subset present)

/-- Initial invariants construct strict source reads for the reached continuation of this actual Scan. -/
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
    (ranges : SourceCurrentConjunctionScanClassPass.Ranges budget records values before fourth memo)
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
  obtain ⟨scanMemos, scanRead, scanValid, scanReady, scanEffects, scanValues, scanCorrect, _⟩ :=
    SourceCurrentAllocatedScanReadValidity.construct actualScan ready available pathsProper formulas solver
      correct ranges.scan memos valid
  cases outcome with
  | some paths =>
      let actual := Reduction.stopped (memo := memo) actualScan
      have read : Reads formulas solver actual memos scanMemos := .stopped scanRead
      obtain ⟨next, receipt⟩ := verified formulas solver inventory read ready admitted available proper fields
        correct stored covered ranges.scan valid
      exact ⟨_, _, _, next, scanMemos, actual, read, receipt⟩
  | none =>
      obtain ⟨requiredInventory, requiredValues, heap, required, _⟩ :=
        SourceCurrentConjunctionRequired.scan_required_complete formulas solver inventory actualScan ready admitted available
          pathsProper pathsActive correct ranges.scan
      obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actualScan
      have retainedFields := retained.fields
      obtain ⟨fuel, readFuel, enough⟩ := required.stable
      have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
      obtain ⟨requiredMemos, requiredRead, requiredValid, _, _⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
        fuel readFuel (SourceEqualitySelectedRequired.paths selected) values requiredValues middle.native.machine.heap heap
          done scanReady.semantic scanReady.costs scanValues scanMemos scanValid
      obtain ⟨results, after, saved, next, final, pass, passRead, _⟩ :=
        SourceCurrentConjunctionRequiredClassPass.finite formulas solver requiredInventory required kept retainedFields.2
          (fun record member => (fields record (retainedFields.1.subset member)).1)
          (fun record member => (fields record (retainedFields.1.subset member)).2.2)
          memo (stored.grows scanEffects.keeps) covered
          (ranges.pass actualScan kept retained fuel readFuel requiredValues heap done) requiredMemos requiredValid
      let actual := Reduction.completed actualScan retained done pass
      have read : Reads formulas solver actual memos final :=
        .completed (retained := retained) (required := done) scanRead requiredRead passRead
      obtain ⟨finalInventory, receipt⟩ := verified formulas solver inventory read ready admitted available proper fields
        correct stored covered ranges.scan valid
      exact ⟨results, after, saved, finalInventory, final, actual, read, receipt⟩

/-- Reached finite plans construct a strict source schedule and its actual receipt. -/
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
    (ranges : SourceCurrentConjunctionScanClassPass.Ranges budget records values before fourth memo)
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

end MicroCFTA.SourceCurrentConjunctionScanClassPassActual
