import MicroCFTA.SourceCurrentAllocatedProbeScan
import MicroCFTA.SourceCurrentAllocatedProbeRequired
import MicroCFTA.SourceCurrentAllocatedProbeClassPass
import MicroCFTA.SourceCurrentAllocatedParentEdge

/-!
# Constructed current local reductions with filtered probes

The construction keeps one actual Scan and its returned global bundles.
Successful scans derive the required forest and the actual class pass.
Stopped scans retain their literal returned heap. Probe preservation is
proved from the actual stages, separately from readiness and cache growth.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeReduction
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

open SourceCurrentConjunctionScanClassPass (Reduction Reads Ranges Receipt)
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

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
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ results after saved next final, ∃ actual : Reduction budget records values before fourth memo outcome results after savedFourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final ∧
      ProbeHeap after.native.machine.heap := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  have scanProbes := SourceCurrentAllocatedProbeScan.scan_heap formulas solver inventory actualScan
    ready admitted available pathsProper correct ranges.scan probes
  obtain ⟨scanMemos, scanInventory, scanReads, scanValid, scanReady, scanAdmitted,
      scanEffects, scanValues, scanCorrect, fourthRetained, sound⟩ :=
    SourceCurrentConjunctionClassScanGlobalMemos.verified formulas solver inventory actualScan ready admitted available
      pathsProper pathsActive correct ranges.scan memos valid
  cases outcome with
  | some paths =>
      have original : paths ∈ records.map SourceEqualityClassOrder.Record.paths :=
        SourceCurrentConjunctionClassScan.stopped_member actualScan
      refine ⟨EqualityLeafProjectionRuntimeEmpty.erase values, middle, memo, scanInventory, scanMemos,
        .stopped actualScan, .stopped scanReads, ?_, scanProbes⟩
      refine ⟨scanReady, scanAdmitted, scanEffects, scanValues,
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
      have requiredProbes := (SourceCurrentAllocatedProbeRequired.requireAll fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues middle.native.machine.heap heap
        requiredDone scanReady.semantic scanReady.costs scanProbes scanValues).2.2.2.1
      have passProbes := SourceCurrentAllocatedProbeClassPass.pass_heap formulas solver requiredInventory passReads
        (fun record member => (keptFields record member).1)
        (fun record member => (keptFields record member).2.2) required.ready required.admitted required.resident
        (SourceCurrentConjunctionRequiredClassPass.selected_domains required kept selectedEq)
        ((stored.grows scanEffects.keeps).grows required.effects.keeps) covered requiredValid requiredProbes
      refine ⟨results, after, saved, next, final,
        .completed actualScan retained requiredDone passActual,
        .completed (retained := retained) (required := requiredDone) firstReads requiredReads passReads, ?_, passProbes⟩
      refine ⟨checked.pass.ready, checked.pass.admitted, scanEffects.trans checked.effects, checked.originals_available,
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
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ outcome results after savedFourth saved next final,
      ∃ actual : Reduction budget records values before fourth memo outcome results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final ∧
      ProbeHeap after.native.machine.heap := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  obtain ⟨outcome, selected, middle, savedFourth, scan, _⟩ := SourceCurrentConjunctionClassScanCompletion.finite
    formulas solver budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth ready available pathsProper correct ranges.scan
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, finalProbes⟩ := from_scan formulas solver inventory budget
    records values before fourth memo scan ready admitted available proper fields correct stored covered ranges memos valid probes
  exact ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt, finalProbes⟩

end MicroCFTA.SourceCurrentAllocatedProbeReduction
