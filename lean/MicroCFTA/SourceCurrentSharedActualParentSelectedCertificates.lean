import MicroCFTA.SourceCurrentSharedActualParentScanNativeStores
import MicroCFTA.SourceCurrentSharedScanReadValidity
import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
import MicroCFTA.SourceCurrentSharedUnionNormalScan
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame

/-!
# Certificates at the actual shared Parent selected cuts

The source Parent receipt retains the same shared Scan, Required and pass
endpoints. Each supplied read bundle is validated at its own returned heap.
Canonical completion identifies physical endpoints only. It does not
change the bounds or bundles of the supplied reads.
-/
namespace MicroCFTA.SourceCurrentSharedActualParentSelectedCertificates
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentSharedScanCallerNumeric (ScanReads)
open SourceCurrentNativeRequestPositivePositions (Support)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem preparation_reads
    {width budget : Nat} {records kept : List SourceEqualityClassOrder.Record} {values results : List Node}
    {before after : Checked width} {fourth saved : Fourth} {memos final : Memos}
    {execution : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth none kept results after saved}
    (reads : SourceCurrentSharedScanRequiredNumeric.Reads execution memos final) :
    ∃ middle heap g s p h n r reader scanMemos,
      SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records before fourth =
        .done (none, kept) middle saved ∧
      SourceEqualityRequiredExecution.requireAll r reader
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
        middle.native.machine.heap = .done results heap ∧
      after = advanceHeap middle heap ∧
      ScanReads budget values records before fourth none kept middle saved memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values results
        middle.native.machine.heap heap scanMemos final := by
  cases reads with
  | @prepared before fourth kept middle saved results heap g s p h n r reader observed required memos scanMemos final first second =>
      exact ⟨middle, heap, g, s, p, h, n, r, reader, scanMemos, observed, required, rfl, first, second⟩

/-- Original prefix resources certify the supplied preparation and its exact returned bundle. -/
theorem prepared_certificates
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List Node) (records : List SourceEqualityClassOrder.Record)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (_coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentSharedScanNumericForecast.Reserved bits budget values.length
      (records.map SourceEqualityClassOrder.Record.paths) (guards before.checked.native.machine.heap) profile)
    {g s p h n r read : Nat} {kept : List SourceEqualityClassOrder.Record}
    {scanned : Checked (bits + 2)} {scanFourth : Fourth} {prepared : List Node}
    {preparedHeap : State Symbol Guard} {preparedMemos : Memos}
    (observed : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
      before.checked before.fourth = .done (none, kept) scanned scanFourth)
    (required : SourceEqualityRequiredExecution.requireAll r read
      (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
      scanned.native.machine.heap = .done prepared preparedHeap)
    (reads : SourceCurrentSharedScanRequiredNumeric.Reads
      (SourceCurrentSharedScanRequiredNumeric.Execution.prepared observed required) memos preparedMemos) :
    ∃ next,
      SourceCurrentConjunctionRequired.Receipt formulas solver next
        (kept.map SourceEqualityClassOrder.Record.paths) values prepared scanned (advanceHeap scanned preparedHeap) ∧
      EndpointMemoGateTrace.Valid preparedHeap preparedMemos ∧
      (∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
        EndpointStatefulGateTrace.ClassTrace source reaches values paths
          scanned.native.machine.heap false scanned.native.machine.heap) ∧
      kept.Sublist records := by
  have known := SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
    initial.ready.semantic.ready.semantic.1.normal.facts
  obtain ⟨outcome, selected, state, saved, next, _canonicalMemos, scan⟩ :=
    SourceCurrentSharedScanCallerNumeric.complete formulas solver inventory (guards before.checked.native.machine.heap)
      budget values records before memos initial frame profile fits available proper active reserved known
  let bound := SourceCurrentSharedScanNumericForecast.fuel budget values.length
    (records.map SourceEqualityClassOrder.Record.paths) (guards before.checked.native.machine.heap) profile
  have completed := scan.run bound bound bound bound bound
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameResult, sameState, sameFourth⟩ :=
    SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique completed observed
  obtain ⟨sameOutcome, sameSelected⟩ := Prod.mk.inj sameResult
  subst outcome selected state saved
  have selectedProper : ∀ path ∈ (kept.map SourceEqualityClassOrder.Record.paths).flatten, path ≠ [] := by
    intro path member
    obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
    obtain ⟨record, keptIn, rfl⟩ := List.mem_map.mp included
    exact proper record (scan.selected.subset keptIn) path present
  have primary : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
      EndpointStatefulGateTrace.ClassTrace source reaches values paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact scan.primary record present
  obtain ⟨results, heap, certificate⟩ := SourceCurrentConjunctionRequired.required_complete formulas solver next
    source reaches (kept.map SourceEqualityClassOrder.Record.paths) values scanned scan.post.context.ready
      scan.post.context.admitted scan.available selectedProper primary
  obtain ⟨fuel, reader, stable⟩ := certificate.stable
  have completedRequired := stable fuel reader (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameValues, sameHeap⟩ := SourceCurrentConjunctionRequiredActual.required_unique completedRequired required
  change heap = preparedHeap at sameHeap
  subst results heap
  obtain ⟨middle, extractedHeap, G, S, P, H, N, R, Reader, scanMemos, scanDone, requiredDone, _endpoint, first, second⟩ :=
    preparation_reads reads
  obtain ⟨_, sameMiddle, _⟩ := SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique scanDone observed
  subst middle
  obtain ⟨_, sameExtractedHeap⟩ := SourceCurrentConjunctionRequiredActual.required_unique requiredDone required
  subst extractedHeap
  have scanValid := SourceCurrentSharedScanReadValidity.scan formulas solver inventory
    (guards before.checked.native.machine.heap) budget values records before memos initial frame profile fits
    available proper reserved known first
  have preparedValid := (SourceCurrentAllocatedRequiredReadValidity.required second scan.post.context.ready.semantic
    scan.post.context.ready.costs scan.available scanValid).1
  exact ⟨next, certificate, preparedValid, primary, scan.selected⟩

private theorem selected_graph
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {width budget : Nat} {inventory : Inventory} {profile : Profile} {symbol : Symbol} {original : Guard}
    {loaded : Allocated} {inherited : EqValue} {values : List Node} {before : Caller width} {after : Checked width}
    {savedFourth : Fourth} {saved : Memo} {result : EdgeValue Symbol Guard} {memos final : Memos}
    (reads : SourceCurrentSharedParentNumeric.Reads formulas solver inventory profile budget symbol original loaded inherited
      values before memos result after savedFourth saved final)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records kept : List SourceEqualityClassOrder.Record} {scanned : Checked width} {scanFourth : Fourth}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.checked.operations).1 =
      .ok (.classes records))
    {g s p h n r e m c : Nat}
    (scanCall : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
      (prefixState before.checked loaded inherited) before.fourth = .done (none, kept) scanned scanFourth)
    {preparedValues : List Node} {preparedHeap : State Symbol Guard} {classAfter : Checked width}
    (requiredCall : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
      scanned.native.machine.heap = .done preparedValues preparedHeap)
    (passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept preparedValues
      (advanceHeap scanned preparedHeap) before.merge = .done result.children classAfter saved) :
    ∃ scanMemos preparedMemos,
    ∃ pass : SourceCurrentAllocatedClassPass.Pass kept preparedValues (advanceHeap scanned preparedHeap)
      before.merge result.children classAfter saved,
      (SourceCurrentAllocatedMkEdge.build symbol loaded result.children classAfter = (.ok result, after) ∧
        savedFourth = scanFourth) ∧
      SourceCurrentSharedScanRequiredNumeric.Reads
        (SourceCurrentSharedScanRequiredNumeric.Execution.prepared scanCall requiredCall) memos preparedMemos ∧
      ScanReads budget values records (prefixState before.checked loaded inherited) before.fourth
        none kept scanned scanFourth memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values preparedValues
        scanned.native.machine.heap preparedHeap scanMemos preparedMemos ∧
      SourceCurrentAllocatedClassPass.PassReads formulas solver pass preparedMemos final := by
  cases reads with
  | rejected test =>
      rw [noncontradictory] at test
      cases test
  | live _ lower built =>
      have localReads := lower.reads
      cases localReads with
      | unchanged =>
          rename_i actual
          have impossible := Except.ok.inj (actual.symm.trans precheck)
          cases impossible
      | emptyChildren =>
          rename_i actual
          have impossible := Except.ok.inj (actual.symm.trans precheck)
          cases impossible
      | classes calls =>
          rename_i originalRecords outcome actual continuation
          have same := Except.ok.inj (actual.symm.trans precheck)
          cases same
          cases calls with
          | stopped first =>
              cases first with
              | @stopped before fourth paths selected reached current G S P H N
                  initial final observed calls =>
                  have same := SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique observed scanCall
                  have impossible := congrArg Prod.fst same.1
                  cases impossible
          | @completed before fourth memo selected prepared middle current children
              classState saved preparation pass initial preparedMemos final first last =>
              cases first with
              | @prepared before fourth selected scanned current requiredValues requiredHeap
                  G S P H N R Read observed required initial actualScanMemos actualRequiredMemos first second =>
                  obtain ⟨sameResult, sameState, sameFourth⟩ :=
                    SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique observed scanCall
                  obtain ⟨_, sameSelected⟩ := Prod.mk.inj sameResult
                  cases sameSelected
                  cases sameState
                  cases sameFourth
                  obtain ⟨sameRequired, sameHeap⟩ := SourceCurrentConjunctionRequiredActual.required_unique required requiredCall
                  cases sameRequired
                  cases sameHeap
                  obtain ⟨E, P, H, M, C, N, stablePass⟩ := SourceCurrentAllocatedClassWorkerCompletion.pass_complete pass
                  have passDone := stablePass E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
                    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
                  obtain ⟨sameChildren, sameClassState, _⟩ :=
                    SourceCurrentAllocatedClassWorkerStability.pass_done_unique passDone passCall
                  cases sameChildren
                  cases sameClassState
                  exact ⟨actualScanMemos, _, pass, ⟨built, rfl⟩,
                    .prepared (observed := scanCall) (required := requiredCall) first second, first, second, last⟩

/-- Original Parent inputs derive the certificates at the same actual selected stage returns. -/
theorem selected_certificates
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List Node) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : SourceCurrentSharedParentNumeric.LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentSharedParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records kept : List SourceEqualityClassOrder.Record} {scanned : Checked (bits + 2)} {scanFourth : Fourth}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.checked.operations).1 =
      .ok (.classes records))
    (scanCall : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
      (prefixState before.checked loaded inherited) before.fourth = .done (none, kept) scanned scanFourth)
    {preparedValues : List Node} {preparedHeap : State Symbol Guard} {classAfter : Checked (bits + 2)}
    (requiredCall : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
      scanned.native.machine.heap = .done preparedValues preparedHeap)
    (passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept preparedValues
      (advanceHeap scanned preparedHeap) before.merge = .done result.children classAfter saved)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
    (supported : Support before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap) :
    ∃ next final own preparedInventory scanMemos preparedMemos,
    ∃ _numeric : SourceCurrentSharedParentNumeric.Receipt formulas solver next profile budget symbol original loaded inherited values
      before memos result after savedFourth saved final,
    ∃ pass : SourceCurrentAllocatedClassPass.Pass kept preparedValues (advanceHeap scanned preparedHeap)
      before.merge result.children classAfter saved,
      (SourceCurrentAllocatedMkEdge.build symbol loaded result.children classAfter = (.ok result, after) ∧ savedFourth = scanFourth) ∧
      SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before.checked own (.classes records) ∧
      ScanReads budget values records (prefixState before.checked loaded inherited) before.fourth
        none kept scanned scanFourth memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values preparedValues
        scanned.native.machine.heap preparedHeap scanMemos preparedMemos ∧
      SourceCurrentAllocatedClassPass.PassReads formulas solver pass preparedMemos final ∧
      SourceCurrentConjunctionRequired.Receipt formulas solver preparedInventory
        (kept.map SourceEqualityClassOrder.Record.paths) values preparedValues scanned (advanceHeap scanned preparedHeap) ∧
      EndpointMemoGateTrace.Valid preparedHeap preparedMemos ∧ kept.Sublist records ∧
      (∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths, EndpointStatefulGateTrace.ClassTrace source reaches values paths
        scanned.native.machine.heap false scanned.native.machine.heap) ∧
      Ready scanned ∧ SourceCurrentConjunctionRowsAllocation.Effects
        (physical (prefixState before.checked loaded inherited)) (physical scanned) ∧
      SourceRecursiveIntersectionKernel.Extension (prefixState before.checked loaded inherited).native.machine scanned.native.machine ∧
      Values scanned.native.machine.heap values ∧ Current scanned ∧ Support scanned.native.machine.heap scanned.native ∧
      Nonempty (History empty scanned.native.machine.heap) ∧ SourceCurrentRequiredUnionNormal.UnionNormal scanned.native.machine.heap := by
  have current : Current before.checked := SourceCurrentConstrainedCapOperandFrame.current frame
  obtain ⟨next, final, numeric, _, _, _selectedScan, scanReady, effects, extension, scanAvailable,
      scanCurrent, scanSupport, scanHistory⟩ :=
    SourceCurrentSharedActualParentScanNativeStores.selected_scan formulas solver inventory budget symbol original loaded
      inherited values before memos initial frame profile fits live reserved observed noncontradictory precheck scanCall current supported causal
  obtain ⟨scanMemos, preparedMemos, pass, assembled, preparation, first, second, last⟩ :=
    selected_graph numeric.reads noncontradictory precheck scanCall requiredCall passCall
  obtain ⟨cached, found, inheritedReady, available⟩ := live noncontradictory
  obtain ⟨own, prefixReceipt⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
  obtain ⟨proper, _, _, _, _, fields⟩ := prefixReceipt.classes records rfl
  have properRecords : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
    intro record member path included
    exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩) path included
  have coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record :=
    fun record member => (fields record member).1
  have active : ∀ record ∈ records, Nontrivial record.paths :=
    fun record member => (fields record member).2.2
  have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
    ⟨prefixReceipt.ready, prefixReceipt.admitted, frame.context, frame.joint, frame.origins⟩
  have prefixFits : Fits profile (prefixState before.checked loaded inherited) :=
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩
  have prefixContext : Context formulas solver inventory
      (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos :=
    ⟨prefixReceipt.ready, prefixReceipt.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge prefixReceipt.effects,
      initial.stored, initial.covered, initial.correct, initial.globals, initial.probes⟩
  have classRoom : SourceCurrentSharedClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile := by
    simpa only [SourceCurrentSharedParentForecast.Reserved, noncontradictory, Bool.false_eq_true, ↓reduceIte,
      SourceCurrentSharedLocalForecast.Reserved, precheck] using reserved
  obtain ⟨preparedInventory, requiredReceipt, preparedValid, primary, selected⟩ :=
    prepared_certificates formulas solver inventory budget values records
      (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos
      prefixContext prefixFrame profile prefixFits available properRecords coherent active classRoom.1 scanCall requiredCall preparation
  have scanNormal := SourceCurrentSharedUnionNormalScan.records g s p h n budget values records
    (prefixState before.checked loaded inherited) before.fourth normal
  rw [scanCall] at scanNormal
  exact ⟨next, final, own, preparedInventory, scanMemos, preparedMemos, numeric, pass, assembled, prefixReceipt,
    first, second, last, requiredReceipt, preparedValid, selected, primary, scanReady, effects, extension,
    scanAvailable, scanCurrent, scanSupport, scanHistory, scanNormal⟩

end MicroCFTA.SourceCurrentSharedActualParentSelectedCertificates
