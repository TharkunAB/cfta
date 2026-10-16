import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
import MicroCFTA.SourceCurrentAllocatedScanReadValidity
import MicroCFTA.SourceCurrentAllocatedScanSourceReads
import MicroCFTA.SourceCurrentConjunctionScanClassPass
import MicroCFTA.SourceCurrentAllocatedLocalReduction
import MicroCFTA.SourceCurrentAllocatedParentEdge

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


/-!
# Receipts for the supplied allocated local reduction

The actual precheck selects the same branch as its derived allocation
receipt. A live branch uses the supplied Scan and class continuation.
The theorem retains its exact children, checked state, and memo tables.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalReductionActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Early returns make no global query; live returns retain the actual stage reads. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {loaded : Allocated} → {inherited : EqValue} →
    {values results : List (Value Symbol Guard)} → {before after : Checked width} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} →
    Reduction budget loaded inherited values before fourth memo results after savedFourth saved → Memos → Memos → Prop where
  | unchanged {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Reduction.unchanged (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | emptyChildren {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Reduction.emptyChildren (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | classes {budget loaded inherited values before fourth memo records outcome results after savedFourth saved actual}
      {continuation : SourceCurrentConjunctionScanClassPass.Reduction budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved} {memos final}
      (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver continuation memos final) :
      Reads formulas solver (Reduction.classes actual continuation) memos final


/-- Source-refined reads retain the actual historical precheck and continuation. -/
theorem Reads.erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    {memos final : Memos} (reads : Reads formulas solver actual memos final) :
    SourceCurrentAllocatedLocalReduction.Reads formulas solver actual memos final := by
  cases reads with
  | unchanged => exact .unchanged (actual := by assumption)
  | emptyChildren => exact .emptyChildren (actual := by assumption)
  | classes actual => exact .classes (actual := by assumption) actual.erase

/-- Only actual live precheck returns require the reached Scan range checks. -/
def Ranges (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) : Prop :=
  ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
    SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth

/-- Existing finite plans supply the smaller actual-verification plan. -/
theorem ranges_of_finite
    {budget : Nat} {loaded : Allocated} {inherited : EqValue} {values : List (Value Symbol Guard)}
    {before : Checked width} {fourth : Fourth} {memo : Memo}
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo) :
    Ranges budget loaded inherited values before fourth := fun records actual => (ranges records actual).scan

omit [DecidableEq (Value Symbol Guard)] in
/-- The actual completed prefix derives its own branch receipt from the current stored field. -/
theorem prefix_verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    {branch : SourceEqualityPrecheck.Branch}
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok branch) :
    ∃ own, SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own branch := by
  obtain ⟨own, chosen, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  have same := Except.ok.inj (receipt.actual.symm.trans actual)
  cases same
  exact ⟨own, receipt⟩

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

/-- Actual local reads derive physical and language receipts without a final invariant premise. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget loaded inherited values before fourth)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final := by
  cases reads with
  | unchanged =>
      rename_i actual
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      refine ⟨inventory, ⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects,
        available, available, rfl, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      exact ⟨id, fun _ _ => Iff.rfl⟩
  | emptyChildren =>
      rename_i actual
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      refine ⟨inventory, ⟨inventory, own, .emptyChildren, checked⟩, checked.ready, checked.admitted, checked.effects,
        available, (SourceEqualityEmptyPropagation.erased_scope before.native.machine.heap values).1,
        List.length_map _, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      have narrows := erased_narrows (SourceEqualityPCSGuard.holds formulas solver) ambient values terms
      exact ⟨narrows, fun guard inheritedSat => False.elim (checked.empty_guard rfl _ guard inheritedSat)⟩
  | classes reads =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨next, receipt⟩ := SourceCurrentConjunctionScanClassPassActual.verified formulas solver inventory
        reads checked.ready checked.admitted available recordsProper fields correct stored covered
          (ranges records checked.actual) valid
      refine ⟨next, ⟨inventory, own, .classes records, checked⟩, receipt.ready, receipt.admitted,
        checked.effects.trans receipt.effects, receipt.originals, receipt.available, receipt.length,
        receipt.stored, receipt.covered, receipt.retained, receipt.globals, receipt.correct,
        receipt.fourthRetained, ?_⟩
      intro ambient symbol terms
      have language := receipt.language ambient symbol terms
      refine ⟨language.1, fun guard _ => language.2 ?_⟩
      have satisfied := (checked.classes_exact records rfl (.node symbol terms)).mpr
        (SourceEqualityPCSGuard.own_sat formulas solver original (.node symbol terms) guard)
      intro record member
      exact satisfied record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)

/-- Initial stored-field invariants and finite plans construct a strict actual local schedule. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final := by
  have checks := ranges_of_finite ranges
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  cases branch with
  | unchanged =>
      let actual : Reduction budget loaded inherited values before fourth memo values
          (prefixState before loaded inherited) fourth memo := .unchanged checked.actual
      have read : Reads formulas solver actual memos memos := .unchanged (actual := checked.actual)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | emptyChildren =>
      let actual : Reduction budget loaded inherited values before fourth memo
          (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before loaded inherited) fourth memo :=
        .emptyChildren checked.actual
      have read : Reads formulas solver actual memos memos := .emptyChildren (actual := checked.actual)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | classes records =>
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, continuation, stageRead, _⟩ :=
        SourceCurrentConjunctionScanClassPassActual.finite formulas solver inventory budget records values
          (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available
          recordsProper fields correct stored covered (ranges records checked.actual) memos valid
      let actual := Reduction.classes checked.actual continuation
      have read : Reads formulas solver actual memos final := .classes (actual := checked.actual) stageRead
      obtain ⟨finalInventory, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨results, after, savedFourth, saved, finalInventory, final, actual, read, receipt⟩

end MicroCFTA.SourceCurrentAllocatedLocalReductionActual


/-!
# Receipts for the supplied actual parent-edge return

The actual raw rejection has no child or local-range premise. A live
return uses the supplied local reads and literal checked constructor.
The returned receipt describes that same edge and full checked state.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentEdgeActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge Receipt RawMeaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Only the reached live local graph demands global memo reads. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {symbol : Symbol} → {original : Guard} → {loaded : Allocated} → {inherited : EqValue} →
    {values : List (Value Symbol Guard)} → {before after : Checked width} → {result : EdgeValue Symbol Guard} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} →
    Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved → Memos → Memos → Prop where
  | rejected {budget symbol original loaded inherited values before fourth memo test memos} :
      Reads formulas solver (Edge.rejected (budget := budget) (symbol := symbol) (original := original)
        (loaded := loaded) (inherited := inherited) (values := values) (before := before)
        (fourth := fourth) (memo := memo) test) memos memos
  | live {budget symbol original loaded inherited values before fourth memo children middle savedFourth saved result after test}
      {reduction : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
        children middle savedFourth saved}
      {built : SourceCurrentAllocatedMkEdge.build symbol loaded children middle = (.ok result, after)} {memos final}
      (reads : SourceCurrentAllocatedLocalReductionActual.Reads formulas solver reduction memos final) :
      Reads formulas solver (Edge.live (original := original) (symbol := symbol) test reduction built) memos final


/-- Source-refined reads retain the literal parent trace and every returned table. -/
theorem Reads.erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    {memos final : Memos} (reads : Reads formulas solver actual memos final) :
    SourceCurrentAllocatedParentEdge.Reads formulas solver actual memos final := by
  cases reads with
  | rejected => exact .rejected (test := by assumption)
  | live actual => exact .live (test := by assumption) (built := by assumption) actual.erase

/-- Initial invariants and reached live inputs derive the receipt for the supplied actual edge. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final := by
  cases reads with
  | rejected =>
      rename_i test
      obtain ⟨_, _, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget symbol original
        loaded inherited values before fourth memo ready admitted test correct stored covered memos valid
      exact ⟨inventory, receipt⟩
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct stored covered ranges valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      refine ⟨next, constructor.ready, constructor.admitted, receipt.effects.trans constructor.effects, constructor.resident,
        receipt.stored.grows constructor.effects.keeps, receipt.covered, receipt.retained,
        SourceQueryUnfoldMemo.valid_grows _ _ receipt.ready.semantic constructor.effects.keeps final receipt.globals,
        SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps savedFourth receipt.correct,
        receipt.fourthRetained, Or.inr ⟨children, middle, receipt.length, constructor⟩, ?_⟩
      intro ambient term
      have edgeLaw := constructor.language storedReady ambient term
      rw [loadedReady.2] at edgeLaw
      have narrows : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
          RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
        intro accepted
        obtain ⟨terms, shape, forest, guard⟩ := edgeLaw.mp accepted
        exact ⟨terms, shape, (receipt.language ambient symbol terms).1 forest, guard⟩
      refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
      rintro ⟨terms, shape, forest, guard⟩
      apply edgeLaw.mpr
      refine ⟨terms, shape, ?_, guard⟩
      have guards : SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true := by
        simpa only [shape] using guard
      have inheritedSat : SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload := by
        simpa only [shape] using inheritedSat
      exact ((receipt.language ambient symbol terms).2 guards inheritedSat).mpr forest

/-- Finite reached plans construct strict source reads and the same actual parent receipt. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after savedFourth saved next final,
      ∃ actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final := by
  have liveInputs : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth :=
    fun test => ⟨cached, found, inheritedReady, available,
      SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (ranges test)⟩
  cases test : contradictory original with
  | true =>
      let actual : Edge budget symbol original loaded inherited values before fourth memo
          (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2
          fourth memo := .rejected test
      have read : Reads formulas solver actual memos memos := .rejected (test := test)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory read ready admitted liveInputs correct stored covered valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | false =>
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨children, middle, savedFourth, saved, next, final, reduction, localRead, receipt⟩ :=
        SourceCurrentAllocatedLocalReductionActual.finite formulas solver inventory budget original loaded inherited values before
          fourth memo ready admitted cached found inheritedReady available correct stored covered (ranges test) memos valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨result, after, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      let actual := Edge.live (original := original) (symbol := symbol) test reduction constructor.actual
      have read : Reads formulas solver actual memos final :=
        .live (test := test) (built := constructor.actual) localRead
      obtain ⟨finalInventory, receipt⟩ := verified formulas solver inventory read ready admitted liveInputs correct stored covered valid
      exact ⟨result, after, savedFourth, saved, finalInventory, final, actual, read, receipt⟩

end MicroCFTA.SourceCurrentAllocatedParentEdgeActual
