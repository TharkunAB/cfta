import MicroCFTA.SourceSynthesisNativeTypeSharedScan
import MicroCFTA.SourceSynthesisNativeTypeRequired
import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceSynthesisActualSharedSelectedProgramFootprints
import MicroCFTA.SourceCurrentSharedLocalNumeric
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentLowerGuardHeapReturns
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion

/-!
# Complete Type annotations through actual shared local reads

The original annotated forest supplies every structural Type route.
The given shared reads retain the literal Scan, Required and pass cuts.
Required has no assigned Program slots. The actual class pass preserves
all forest routes, including the empty route that states full annotation.
Precheck selects the same unchanged, erased or classes branch.
No range plan, source Program schema or future result is an input.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedLocalWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
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
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "NativeReady" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
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

private theorem paths_of_typed (lib : Library) {values : List Node}
    (typed : ∀ value ∈ values, Annotated (Origin lib) value) :
    ∀ path, ForestPath (Origin lib) path values := by
  intro path
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
    {formulas solver inventory guard loaded inherited before own branch memo}
    (receipt : Receipt (width := width) formulas solver inventory guard loaded inherited before own branch)
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

section Source
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before after : Checked width}
variable {budget : Nat} {values results : List Node} {fourth savedFourth : Fourth} {memo saved : Memo}
variable {memos final : Memos}

/-- Actual shared class reads retain full annotations on every returned Type operand. -/
theorem classes {records : List Record} {outcome : Option EqualityNormalize.Class}
    {execution : SourceCurrentSharedClassesNumeric.Execution budget records values
      (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (ready : Ready lib (initial before memo))
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (typed : ∀ value ∈ values, Annotated (Origin lib) value)
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ value ∈ results, Annotated (Origin lib) value := by
  have entry := prefix_ready lib receipt ready
  have recordPaths := fun (_record : Record) (_member : _record ∈ records) (path : EqualityNormalize.Path)
      (_included : path ∈ _record.paths) => paths_of_typed lib typed (path.map Int.ofNat)
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
      exact ⟨finalReady, receipt.extension.trans extension, returned, resultClosed, finalGuards, routes []⟩
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
          obtain ⟨nextReady, first, middleAvailable, middleClosed, _length, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun _ => False)
              (before := initial scanned memo) required compiled scannedReady known closed
              (fun index value found _ => typed value (List.mem_of_getElem? found))
              (fun _ _ _ assigned => False.elim assigned) (fun _ _ _ assigned => False.elim assigned)
          have middleTyped : ∀ value ∈ middle, Annotated (Origin lib) value := by
            intro value member
            obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
            exact (slots index value found).2 (by simp)
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs
              nextReady.physicalMemo nextReady.typedMemo
          have coherent := SourceSynthesisActualSharedSelectedProgramFootprints.selected_regions receipt scan
            (fun _ => True) (fun _ _ => True.intro)
          obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
            SourceSynthesisNativeTypeClassPass.pass lib passed classReady middleAvailable middleClosed
              (fun record member => (coherent record member).1)
              (fun _ _ path _ => paths_of_typed lib middleTyped (path.map Int.ofNat))
          have finalGuards := pass_guards lib passed classReady middleAvailable requiredGuards
          exact ⟨finalReady, receipt.extension.trans (extension.trans (first.trans last)),
            returned, resultClosed, finalGuards, routes [] middleTyped⟩

/-- Each given shared reduce receipt retains the same precheck branch and complete Type forest. -/
theorem reduce {branch : SourceEqualityPrecheck.Branch}
    {reduction : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
      before fourth memo results after savedFourth saved}
    (receipt : Receipt formulas solver inventory guard loaded inherited before own branch)
    (ready : Ready lib (initial before memo))
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (typed : ∀ value ∈ values, Annotated (Origin lib) value)
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver reduction memos final) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ value ∈ results, Annotated (Origin lib) value := by
  cases actual with
  | @unchanged before fourth memo observed memos =>
      have same := Except.ok.inj (observed.symm.trans receipt.actual)
      cases same
      exact ⟨prefix_ready lib receipt ready, receipt.extension, available, closed, guards, typed⟩
  | @emptyChildren before fourth memo observed memos =>
      have same := Except.ok.inj (observed.symm.trans receipt.actual)
      cases same
      obtain ⟨returned, resultClosed, routes⟩ := erased (Origin lib) values (prefixState before loaded inherited).native.machine.heap
      exact ⟨prefix_ready lib receipt ready, receipt.extension, returned, resultClosed, guards, routes []⟩
  | @classes before fourth memo records outcome results after savedFourth saved observed continuation memos final calls =>
      have same := Except.ok.inj (observed.symm.trans receipt.actual)
      cases same
      exact classes lib formulas solver receipt ready available closed guards typed calls

end Source
end MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedLocalWorker
