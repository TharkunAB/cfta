import MicroCFTA.SourceSynthesisNativeTypeSharedLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeHereditaryClassFields
import MicroCFTA.SourceSynthesisNativeTypeHereditaryRequired
import MicroCFTA.SourceSynthesisNativeTypeSharedScan
import MicroCFTA.SourceSynthesisSharedTypeRequiredRoutes
import MicroCFTA.SourceCurrentSharedClassesNumeric
import MicroCFTA.SourceCurrentSharedLocalNumeric

/-!
# Recursive mixed fields at actual shared local returns

The actual source footprint protects every later Program child. Required
and the tail-first class pass retain complete recursive Program fields.
The same return retains shared readiness, guard profile and source Type routes.
Stopped scans return Empty at every slot. Source receipts, initial fields,
and actual shared read receipts remain explicit premises.
These laws do not establish all reached inputs or completion.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditarySharedLocalWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceEqualityClassOrder (Record)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "NativeReady" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable {width : Nat}

private theorem erased_slots (valid : Guard → Prop) (literal : String → Symbol) (assigned : Nat → Prop) (values : List Node) :
    ∀ index value, (EqualityLeafProjectionRuntimeEmpty.erase values)[index]? = some value →
      (assigned index → ValueFields valid literal value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value found
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? found)
  exact ⟨fun _ => .empty, fun _ => .empty⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Node] in
private theorem prefix_ready (lib : Library)
    {formulas solver inventory guard loaded inherited before own records memo}
    (receipt : Receipt (width := width) formulas solver inventory guard loaded inherited before own (.classes records))
    (ready : Ready lib (initial before memo)) :
    Ready lib (initial (prefixState before loaded inherited) memo) := by
  have checked : NativeReady lib (prefixState before loaded inherited) :=
    ⟨receipt.ready.good, receipt.ready.semantic, ready.checked.scopes, ready.checked.idle,
      ⟨ready.checked.stored.constructors, ready.checked.stored.native⟩⟩
  exact SourceSynthesisNativeTypeSharedState.initial lib _ _ checked receipt.ready.costs ready.physicalMemo ready.typedMemo

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem scanned_ready (lib : Library) {before after : Checked width} {memo : Memo}
    (ready : Ready lib (initial before memo)) (checked : NativeReady lib after)
    (costs : CostHeap after.native.machine.heap) (extension : Extension before.native.machine after.native.machine) :
    Ready lib (initial after memo) := by
  have kept : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap :=
    ⟨checked.semantic.ready, extension.heap, extension.history⟩
  exact SourceSynthesisNativeTypeSharedState.initial lib _ _ checked costs (ready.physicalMemo.grows kept) ready.typedMemo

private theorem classes_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List Node} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {records : List Record}
    {memos final : EndpointMemoGateTrace.Memos}
    {execution : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
      before fourth memo results after savedFourth saved}
    (branch : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok (.classes records))
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final) :
    ∃ outcome, ∃ continuation : SourceCurrentSharedClassesNumeric.Execution budget records values
      (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved,
      SourceCurrentSharedClassesNumeric.Reads formulas solver continuation memos final := by
  cases actual with
  | @unchanged before fourth memo observed memos =>
      rw [observed] at branch
      cases branch
  | @emptyChildren before fourth memo observed memos =>
      rw [observed] at branch
      cases branch
  | @classes before fourth memo selected outcome results after savedFourth saved observed continuation memos final calls =>
      have same : selected = records :=
        SourceEqualityPrecheck.Branch.classes.inj (Except.ok.inj (observed.symm.trans branch))
      subst selected
      exact ⟨outcome, continuation, calls⟩

section Source
variable (lib : Library) (literal : String → Symbol) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before after : Checked width}
variable {records : List Record} {budget : Nat} {values results : List Node}
variable {fourth savedFourth : Fourth} {memo saved : Memo}
variable (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
variable (ready : Ready lib (initial before memo))
variable (available : Values before.native.machine.heap values) (closed : ClosedValues values)
variable (guards : GuardHeap (Origin lib) before.native.machine.heap)
variable {memos final : EndpointMemoGateTrace.Memos}

section Application
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value)
include occurrence receipt ready available closed typed fields guards

private theorem application_completed
    {kept : List Record} {scanned : Checked width} {scanFourth : Fourth}
    {scanMemos : EndpointMemoGateTrace.Memos} {r h : Nat}
    {prepared : List Node} {heap : State Symbol Guard}
    (scanRun : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (prefixState before loaded inherited) fourth none kept scanned scanFourth memos scanMemos)
    (required : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap =
        .done prepared heap)
    (passed : SourceCurrentAllocatedClassPass.Pass kept prepared (advanceHeap scanned heap) memo results after saved) :
    ∀ index value, results[index]? = some value →
        ((index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.applicationRegion
    (SourceSynthesisGuardRegions.application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fun assigned => (fields index value found assigned).fields) (typed index value found)
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.application_paths (Origin lib) (fun index => index = 2 ∨ index = 3)
      values (by decide) inputSlots path ((original record member).2 path included)
  obtain ⟨checked, costs, scanExtension, _scanGuards, known⟩ :=
    SourceSynthesisNativeTypeSharedScan.scan lib scanRun entry.checked entry.costs available closed recordPaths guards
  have scannedReady := scanned_ready lib entry checked costs scanExtension
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        exact SourceSynthesisActualSharedSelectedProgramFootprints.application_annotation_only types function argument
          sourceName sourceChildren occurrence receipt scanRun compiled index assigned found
      obtain ⟨nextReady, _, middleAvailable, middleClosed, _, slots⟩ :=
        SourceSynthesisNativeTypeHereditaryRequired.requireAll lib literal (fun index => index = 2 ∨ index = 3)
          (before := initial scanned memo) required compiled scannedReady known closed typed fields only
      have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
        SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs nextReady.physicalMemo nextReady.typedMemo
      obtain ⟨_, _, selected⟩ := SourceSynthesisSharedTypeRequiredRoutes.application_requireAll (Origin lib)
        types function argument sourceName sourceChildren occurrence receipt scanRun required checked.semantic costs
        known closed checked.stored.constructors typed (fun index value found assigned => (fields index value found assigned).fields)
      have coherent := fun record member => (selected record member).1
      have paths := fun record member => (selected record member).2
      apply SourceSynthesisNativeTypeHereditaryClassFields.pass_fields lib literal (fun index => index = 2 ∨ index = 3)
        passed classReady middleAvailable middleClosed coherent paths
      · intro record member index assigned childIndex nonzero
        exact (SourceSynthesisActualSharedSelectedProgramFootprints.application_footprint types function argument
          sourceName sourceChildren occurrence receipt scanRun member index assigned).2 childIndex nonzero
      · exact fun index value found => (slots index value found).2
      · exact fun index value found => (slots index value found).1

/-- Actual application class reduction retains every recursive mixed returned slot. -/
theorem application_classes
    {outcome : Option EqualityNormalize.Class}
    {execution : SourceCurrentSharedClassesNumeric.Execution budget records values
      (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        ((index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  obtain ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes⟩ :=
    SourceSynthesisNativeTypeSharedLocalWorker.application_classes
      (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
      (available := available) (closed := closed) (guards := guards)
      (types := types) (function := function) (argument := argument) (sourceName := sourceName)
      (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed)
      (fields := fun index value found assigned => (fields index value found assigned).fields) actual
  refine ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes, ?_⟩
  cases actual with
  | stopped preparation =>
      cases preparation with
      | stopped scan => exact erased_slots (Origin lib) literal (fun index => index = 2 ∨ index = 3) values
  | completed preparation passReads =>
      cases preparation with
      | prepared scan requiredReads =>
          exact application_completed (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
            (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards)
            (types := types) (function := function) (argument := argument) (sourceName := sourceName)
            (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) scan (by assumption) (by assumption)

/-- The actual application reduce's classes branch retains all recursive mixed slots. -/
theorem application_reduce
    {execution : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
      before fourth memo results after savedFourth saved}
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        ((index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  obtain ⟨outcome, continuation, calls⟩ := classes_reads receipt.actual actual
  exact application_classes (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards)
    (types := types) (function := function) (argument := argument) (sourceName := sourceName)
    (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) calls
end Application

section Filter
variable (candidates goal : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → index = 1 → ValueFields (Origin lib) literal value)
include occurrence receipt ready available closed typed fields guards

private theorem filter_completed
    {kept : List Record} {scanned : Checked width} {scanFourth : Fourth}
    {scanMemos : EndpointMemoGateTrace.Memos} {r h : Nat}
    {prepared : List Node} {heap : State Symbol Guard}
    (scanRun : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (prefixState before loaded inherited) fourth none kept scanned scanFourth memos scanMemos)
    (required : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap =
        .done prepared heap)
    (passed : SourceCurrentAllocatedClassPass.Pass kept prepared (advanceHeap scanned heap) memo results after saved) :
    ∀ index value, results[index]? = some value →
        (index = 1 → ValueFields (Origin lib) literal value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.filterRegion
    (SourceSynthesisGuardRegions.filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fun assigned => (fields index value found assigned).fields) (typed index value found)
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.filter_paths (Origin lib) (fun index => index = 1)
      values (by decide) inputSlots path ((original record member).2 path included)
  obtain ⟨checked, costs, scanExtension, _scanGuards, known⟩ :=
    SourceSynthesisNativeTypeSharedScan.scan lib scanRun entry.checked entry.costs available closed recordPaths guards
  have scannedReady := scanned_ready lib entry checked costs scanExtension
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
  | node entries =>
      have only : ∀ (index : Nat) children,
          SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
          index = 1 → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
        intro index children found assigned
        subst index
        exact SourceSynthesisActualSharedSelectedProgramFootprints.filter_annotation_only candidates goal
          sourceName sourceChildren occurrence receipt scanRun compiled found
      obtain ⟨nextReady, _, middleAvailable, middleClosed, _, slots⟩ :=
        SourceSynthesisNativeTypeHereditaryRequired.requireAll lib literal (fun index => index = 1)
          (before := initial scanned memo) required compiled scannedReady known closed typed fields only
      have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
        SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs nextReady.physicalMemo nextReady.typedMemo
      obtain ⟨_, _, selected⟩ := SourceSynthesisSharedTypeRequiredRoutes.filter_requireAll (Origin lib)
        candidates goal sourceName sourceChildren occurrence receipt scanRun required checked.semantic costs
        known closed checked.stored.constructors typed (fun index value found assigned => (fields index value found assigned).fields)
      have coherent := fun record member => (selected record member).1
      have paths := fun record member => (selected record member).2
      apply SourceSynthesisNativeTypeHereditaryClassFields.pass_fields lib literal (fun index => index = 1)
        passed classReady middleAvailable middleClosed coherent paths
      · intro record member index assigned childIndex nonzero
        subst index
        exact (SourceSynthesisActualSharedSelectedProgramFootprints.filter_footprint candidates goal
          sourceName sourceChildren occurrence receipt scanRun member).2 childIndex nonzero
      · exact fun index value found => (slots index value found).2
      · exact fun index value found => (slots index value found).1

/-- Actual filter class reduction retains every recursive mixed returned slot. -/
theorem filter_classes
    {outcome : Option EqualityNormalize.Class}
    {execution : SourceCurrentSharedClassesNumeric.Execution budget records values
      (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        (index = 1 → ValueFields (Origin lib) literal value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  obtain ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes⟩ :=
    SourceSynthesisNativeTypeSharedLocalWorker.filter_classes
      (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
      (available := available) (closed := closed) (guards := guards)
      (candidates := candidates) (goal := goal) (sourceName := sourceName) (sourceChildren := sourceChildren)
      (occurrence := occurrence) (typed := typed)
      (fields := fun index value found assigned => (fields index value found assigned).fields) actual
  refine ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes, ?_⟩
  cases actual with
  | stopped preparation =>
      cases preparation with
      | stopped scan => exact erased_slots (Origin lib) literal (fun index => index = 1) values
  | completed preparation passReads =>
      cases preparation with
      | prepared scan requiredReads =>
          exact filter_completed (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
            (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards)
            (candidates := candidates) (goal := goal) (sourceName := sourceName)
            (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) scan (by assumption) (by assumption)

/-- The actual filter reduce's classes branch retains all recursive mixed slots. -/
theorem filter_reduce
    {execution : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
      before fourth memo results after savedFourth saved}
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        (index = 1 → ValueFields (Origin lib) literal value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  obtain ⟨outcome, continuation, calls⟩ := classes_reads receipt.actual actual
  exact filter_classes (lib := lib) (literal := literal) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards)
    (candidates := candidates) (goal := goal) (sourceName := sourceName)
    (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) calls
end Filter

end Source
end MicroCFTA.SourceSynthesisNativeTypeHereditarySharedLocalWorker
