import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
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
    True := by
  cases reads <;> trace_state <;> trivial

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
    True := by
  cases reads <;> trace_state <;> trivial

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
    True := by
  cases reads <;> trace_state <;> trivial

end MicroCFTA.SourceCurrentAllocatedParentEdgeActual
