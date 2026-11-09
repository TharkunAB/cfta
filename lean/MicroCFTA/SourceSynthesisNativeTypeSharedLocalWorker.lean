import MicroCFTA.SourceSynthesisNativeTypeSharedScan
import MicroCFTA.SourceSynthesisNativeTypeSharedRequiredPass
import MicroCFTA.SourceCurrentSharedLocalNumeric
import MicroCFTA.SourceCurrentLowerGuardHeapReturns
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion

/-!
# Type facts through the actual shared local reads

Ordered shared reads retain the exact Scan, Required and class-pass states.
Source guards derive the initial and selected Type routes. The unchanged
class-pass graph supplies its own literal execution for guard preservation.
A stopped Scan erases the original forest. The reduce laws cover only the
precheck's classes branch.

Current source occurrences, precheck receipts, mixed input fields and
actual shared reads remain premises. These laws do not prove completion,
failure-prefix preservation or all reached source classifications.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedLocalWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
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
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem erased (valid : Guard → Prop) (values : List Node)
    (heap : InternedConstructorTemplates.State Symbol Guard) :
    Values heap (EqualityLeafProjectionRuntimeEmpty.erase values) ∧
      ClosedValues (EqualityLeafProjectionRuntimeEmpty.erase values) ∧
      ∀ path, ForestPath valid path (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  have typed : ∀ value ∈ EqualityLeafProjectionRuntimeEmpty.erase values, Annotated valid value := by
    intro value member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact .empty
  refine ⟨?_, ?_, ?_⟩
  · intro value member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact empty_available heap
  · intro value member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    rfl
  · intro path
    cases path with
    | nil => exact typed
    | cons index path =>
        intro value found
        exact .annotated path value (typed value (SourceEqualityProjectionGraph.select_member found))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem stopped_data
    {formulas solver budget records values before fourth memo paths results after savedFourth saved memos final}
    {execution : SourceCurrentSharedClassesNumeric.Execution (width := width)
      budget records values before fourth memo (some paths) results after savedFourth saved}
    (reads : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    ∃ kept, SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before fourth
        (some paths) kept after savedFourth memos final ∧
      results = EqualityLeafProjectionRuntimeEmpty.erase values ∧ saved = memo := by
  cases reads with
  | stopped calls =>
      cases calls with
      | stopped scan => exact ⟨_, scan, rfl, rfl⟩

omit [DecidableEq Node] in
private theorem pass_graph
    {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records values before memo results after saved}
    (_reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final) :
    SourceCurrentAllocatedClassPass.Pass records values before memo results after saved := actual

private theorem completed_data
    {formulas solver budget records values before fourth memo results after savedFourth saved memos final}
    {execution : SourceCurrentSharedClassesNumeric.Execution (width := width)
      budget records values before fourth memo none results after savedFourth saved}
    (reads : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    ∃ kept scanned middle heap r read scanMemos passMemos,
      SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before fourth
        none kept scanned savedFourth memos scanMemos ∧
      SourceEqualityRequiredExecution.requireAll r read
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values
          scanned.native.machine.heap = .done middle heap ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle
          scanned.native.machine.heap heap scanMemos passMemos ∧
      SourceCurrentAllocatedClassPass.Pass kept middle (advanceHeap scanned heap) memo results after saved := by
  cases reads with
  | completed first last =>
      cases first with
      | prepared scan requiredReads =>
          rename_i r read _ _ required _
          exact ⟨_, _, _, _, r, read, _, _, scan, required, requiredReads, pass_graph last⟩

omit [DecidableEq Node] in
private theorem pass_guards (lib : Library)
    {records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassPass.Pass (width := width) records values before memo results after saved)
    (ready : Ready lib (initial before memo))
    (available : Values before.native.machine.heap values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    GuardHeap (Origin lib) after.native.machine.heap := by
  obtain ⟨e, p, h, m, c, n, run⟩ := SourceCurrentAllocatedClassWorkerCompletion.pass_complete actual
  have operationGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked ready.checked.good)
      ready.checked.semantic ready.costs
  exact SourceCurrentLowerGuardHeapReturns.class_pass (Origin lib)
    (run e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    operationGood ready.physicalMemo available guards

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
    {memos final : Memos}
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
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before after : Checked width}
variable {records : List Record} {budget : Nat} {values results : List Node}
variable {fourth savedFourth : Fourth} {memo saved : Memo}
variable (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
variable (ready : Ready lib (initial before memo))
variable (available : Values before.native.machine.heap values) (closed : ClosedValues values)
variable (guards : GuardHeap (Origin lib) before.native.machine.heap)
variable {memos final : Memos} {outcome : Option EqualityNormalize.Class}
variable {execution : SourceCurrentSharedClassesNumeric.Execution budget records values
  (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
variable {reduction : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
  before fourth memo results after savedFourth saved}

section Application
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value)
include occurrence receipt ready available closed typed fields guards

/-- Actual shared application class reads derive the returned Type state and source routes. -/
theorem application_classes
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.applicationRegion
    (SourceSynthesisGuardRegions.application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fields index value found) (typed index value found)
  have sourcePaths := (SourceSynthesisGuardRegions.application_guard_endpoints types function argument
    sourceName guard sourceChildren occurrence).2
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.application_paths (Origin lib) (fun index => index = 2 ∨ index = 3)
      values (by decide) inputSlots path ((original record member).2 path included)
  cases outcome with
  | some paths =>
      obtain ⟨kept, scan, sameResults, sameMemo⟩ := stopped_data actual
      subst results
      subst saved
      obtain ⟨checked, costs, extension, finalGuards, _known⟩ :=
        SourceSynthesisNativeTypeSharedScan.scan lib scan entry.checked entry.costs
          available closed recordPaths guards
      have finalReady := scanned_ready lib entry checked costs extension
      obtain ⟨returned, resultClosed, routes⟩ := erased (Origin lib) values after.native.machine.heap
      exact ⟨finalReady, receipt.extension.trans extension, returned, resultClosed, finalGuards,
        fun path _ => routes (path.map Int.ofNat)⟩
  | none =>
      obtain ⟨kept, scanned, middle, heap, r, read, scanMemos, passMemos,
        scan, required, requiredReads, passed⟩ := completed_data actual
      obtain ⟨checked, costs, extension, scanGuards, known⟩ :=
        SourceSynthesisNativeTypeSharedScan.scan lib scan entry.checked entry.costs
          available closed recordPaths guards
      have scannedReady := scanned_ready lib entry checked costs extension
      have requiredGuards := (SourceCurrentRequiredGuard.requireAll (Origin lib) requiredReads
        checked.semantic costs known scanGuards).1
      cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
      | node entries =>
          have only : ∀ (index : Nat) children,
              SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
              (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
            intro index children found selected
            exact SourceSynthesisActualSharedSelectedProgramFootprints.application_annotation_only
              types function argument sourceName sourceChildren occurrence receipt scan compiled index selected found
          obtain ⟨nextReady, first, middleAvailable, middleClosed, _length, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 2 ∨ index = 3)
              (before := initial scanned memo) required compiled scannedReady known closed typed fields only
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs
              nextReady.physicalMemo nextReady.typedMemo
          obtain ⟨_stored, _length, selected⟩ := SourceSynthesisSharedTypeRequiredRoutes.application_requireAll (Origin lib)
            types function argument sourceName sourceChildren occurrence receipt scan required checked.semantic costs
            known closed checked.stored.constructors typed fields
          obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
            SourceSynthesisNativeTypeClassPass.pass lib passed classReady middleAvailable middleClosed
              (fun record member => (selected record member).1)
              (fun record member => (selected record member).2)
          have finalGuards := pass_guards lib passed classReady middleAvailable requiredGuards
          refine ⟨finalReady, receipt.extension.trans (extension.trans (first.trans last)),
            returned, resultClosed, finalGuards, ?_⟩
          intro path member
          exact routes (path.map Int.ofNat)
            (SourceSynthesisTypeRequiredRoutes.application_paths (Origin lib) (fun index => index = 2 ∨ index = 3)
              middle (by decide) slots path (sourcePaths path member))

/-- The shared reduce reads select the same receipt's literal classes branch. -/
theorem application_reduce
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver reduction memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  obtain ⟨selectedOutcome, continuation, calls⟩ := classes_reads receipt.actual actual
  exact application_classes (lib := lib) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed)
    (guards := guards) (types := types) (function := function) (argument := argument)
    (sourceName := sourceName) (sourceChildren := sourceChildren) (occurrence := occurrence)
    (typed := typed) (fields := fields) (outcome := selectedOutcome) (execution := continuation) calls
end Application

section Filter
variable (candidates goal : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → index = 1 → AnnotationFields (Origin lib) value)
include occurrence receipt ready available closed typed fields guards

/-- Actual shared filter class reads derive the returned Type state and source routes. -/
theorem filter_classes
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.filterRegion
    (SourceSynthesisGuardRegions.filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fields index value found) (typed index value found)
  have sourcePaths := (SourceSynthesisGuardRegions.filter_guard_endpoints candidates goal
    sourceName guard sourceChildren occurrence).2
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.filter_paths (Origin lib) (fun index => index = 1)
      values (by decide) inputSlots path ((original record member).2 path included)
  cases outcome with
  | some paths =>
      obtain ⟨kept, scan, sameResults, sameMemo⟩ := stopped_data actual
      subst results
      subst saved
      obtain ⟨checked, costs, extension, finalGuards, _known⟩ :=
        SourceSynthesisNativeTypeSharedScan.scan lib scan entry.checked entry.costs
          available closed recordPaths guards
      have finalReady := scanned_ready lib entry checked costs extension
      obtain ⟨returned, resultClosed, routes⟩ := erased (Origin lib) values after.native.machine.heap
      exact ⟨finalReady, receipt.extension.trans extension, returned, resultClosed, finalGuards,
        fun path _ => routes (path.map Int.ofNat)⟩
  | none =>
      obtain ⟨kept, scanned, middle, heap, r, read, scanMemos, passMemos,
        scan, required, requiredReads, passed⟩ := completed_data actual
      obtain ⟨checked, costs, extension, scanGuards, known⟩ :=
        SourceSynthesisNativeTypeSharedScan.scan lib scan entry.checked entry.costs
          available closed recordPaths guards
      have scannedReady := scanned_ready lib entry checked costs extension
      have requiredGuards := (SourceCurrentRequiredGuard.requireAll (Origin lib) requiredReads
        checked.semantic costs known scanGuards).1
      cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
      | node entries =>
          have only : ∀ (index : Nat) children,
              SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
              (index = 1) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
            intro index children found selected
            subst index
            exact SourceSynthesisActualSharedSelectedProgramFootprints.filter_annotation_only
              candidates goal sourceName sourceChildren occurrence receipt scan compiled found
          obtain ⟨nextReady, first, middleAvailable, middleClosed, _length, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 1)
              (before := initial scanned memo) required compiled scannedReady known closed typed fields only
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs
              nextReady.physicalMemo nextReady.typedMemo
          obtain ⟨_stored, _length, selected⟩ := SourceSynthesisSharedTypeRequiredRoutes.filter_requireAll (Origin lib)
            candidates goal sourceName sourceChildren occurrence receipt scan required checked.semantic costs
            known closed checked.stored.constructors typed fields
          obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
            SourceSynthesisNativeTypeClassPass.pass lib passed classReady middleAvailable middleClosed
              (fun record member => (selected record member).1)
              (fun record member => (selected record member).2)
          have finalGuards := pass_guards lib passed classReady middleAvailable requiredGuards
          refine ⟨finalReady, receipt.extension.trans (extension.trans (first.trans last)),
            returned, resultClosed, finalGuards, ?_⟩
          intro path member
          exact routes (path.map Int.ofNat)
            (SourceSynthesisTypeRequiredRoutes.filter_paths (Origin lib) (fun index => index = 1)
              middle (by decide) slots path (sourcePaths path member))

/-- The shared reduce reads select the same receipt's literal classes branch. -/
theorem filter_reduce
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver reduction memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results := by
  obtain ⟨selectedOutcome, continuation, calls⟩ := classes_reads receipt.actual actual
  exact filter_classes (lib := lib) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed)
    (guards := guards) (candidates := candidates) (goal := goal)
    (sourceName := sourceName) (sourceChildren := sourceChildren) (occurrence := occurrence)
    (typed := typed) (fields := fields) (outcome := selectedOutcome) (execution := continuation) calls
end Filter

end Source
end MicroCFTA.SourceSynthesisNativeTypeSharedLocalWorker
