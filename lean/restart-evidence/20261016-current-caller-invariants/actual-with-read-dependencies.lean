import MicroCFTA.SourceCurrentAllocatedGateReadValidity
import MicroCFTA.SourceCurrentAllocatedSeededReadValidity
import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
import MicroCFTA.SourceCurrentAllocatedScanSourceReads
import MicroCFTA.SourceCurrentAllocatedPrimaryCompletion
import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
import MicroCFTA.SourceCurrentConjunctionScanClassPass
import MicroCFTA.SourceCurrentAllocatedLocalReduction
import MicroCFTA.SourceCurrentAllocatedParentEdge

/-!
# Validity of supplied current class-query reads

The secondary gate, seeded fold, and conjunction call retain the exact
returned bundle supplied to each next phase. Physical effects come from
the actual source graphs and reached word checks.
-/
namespace MicroCFTA.SourceCurrentAllocatedQueryReadValidity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentConjunctionQueryGlobalMemos (QueryReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A supplied query receipt derives validity of its actual final tables and its physical receipt. -/
theorem query
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {value : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    {gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor}
    {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) value middle}
    {call : SourceCurrentConjunctionMemo.Call budget memo value (physical middle) answer after saved}
    {memos final : Memos} (reads : QueryReads gate seeded call memos final)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor))
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.heap final ∧ Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  cases reads with
  | run gateRead seedRead callRead =>
      have initialReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
      obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
        SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
          (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
      have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate initialReady available
      have advancedReady := SourceCurrentConjunctionClassScan.advance_ready before ⟨anchor, before.operations⟩ ready first.1
      have gateKept := SourceCurrentAllocatedGateReadValidity.secondary_class gateRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      obtain ⟨chosen, reached, completed, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
        SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values gate ready.good initialReady
          ready.scopedCache ready.idle available proper ranges
      obtain ⟨rfl, rfl⟩ := seeded.unique completed
      have seedValid := SourceCurrentAllocatedSeededReadValidity.seeded unconstrained anchor anchorSemantic anchorReady
        seedRead ranges advancedReady.good first.1.ready advancedReady.scopedCache advancedReady.idle anchorValues
        (grows_refl anchor) (by
          intro path member
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          exact supported original present) gateKept.valid
      have queryReady : Ready middle :=
        ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
      have finalValid := SourceCurrentAllocatedConjunctionReadValidity.call callRead queryEffects.ready queryAvailable seedValid.1
      obtain ⟨finalReady, callEffects, finalCorrect, _, retained⟩ :=
        SourceCurrentConjunctionClassScan.memo_effects formulas solver call queryReady queryAvailable queryCorrect
      exact ⟨finalValid.1, finalReady, queryEffects.trans callEffects,
        (fun value member => callEffects.keeps.available value (queryEffects.keeps.available value (available value member))),
        finalCorrect, retained⟩

end MicroCFTA.SourceCurrentAllocatedQueryReadValidity


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


end MicroCFTA.SourceCurrentAllocatedScanReadValidity


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

end MicroCFTA.SourceCurrentAllocatedParentEdgeActual
