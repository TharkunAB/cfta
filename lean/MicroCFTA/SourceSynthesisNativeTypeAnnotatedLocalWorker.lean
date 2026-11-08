import MicroCFTA.SourceSynthesisNativeTypeLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker

/-!
# Annotated Type forests at actual local returns

Every input value has a complete Type annotation. All structural paths
therefore have Type routes. The literal Scan, Required and class pass
retain the annotation at the empty path. All precheck branches retain
the same checked state, fourth memo and Merge memo as actual execution.

Successful execution, an actual precheck receipt, initial state facts and
reached range plans remain premises. These laws do not prove completion,
all reached input classifications, failure safety or a total work bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeAnnotatedLocalWorker
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
variable {width : Nat}

private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {result : B} {after : Checked width} {fourth : Fourth} {memo : Memo}
    (actual : first.bind next = .done result after fourth memo) :
    ∃ value middle saved warm, first = .done value middle saved warm ∧
      next value middle saved warm = .done result after fourth memo := by
  cases first with
  | done value middle saved warm => exact ⟨value, middle, saved, warm, rfl, actual⟩
  | failed => cases actual

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

private theorem scan_done {g s p h n budget records values before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.scan (width := width) g s p h n budget records values before fourth memo =
      .done result after saved current) :
    SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
      .done result after saved ∧ current = memo := by
  cases observed : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.scan, observed] at actual; cases actual
  | done output checked completed =>
      simp only [SourceCurrentAllocatedLocalWorker.scan, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem required_done {r h paths values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.required (width := width) r h paths values before fourth memo =
      .done results after saved current) :
    ∃ heap, SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap = .done results heap ∧
      after = advanceHeap before heap ∧ saved = fourth ∧ current = memo := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentAllocatedLocalWorker.required, observed] at actual
      cases actual
  | done output heap =>
      simp only [SourceCurrentAllocatedLocalWorker.required, observed] at actual
      cases actual
      exact ⟨heap, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Node] in
private theorem pass_done {e p h m c n records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.pass (width := width) e p h m c n records values before fourth memo =
      .done results after saved current) :
    SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo = .done results after current ∧
      saved = fourth := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.pass, observed] at actual; cases actual
  | done output checked completed =>
      simp only [SourceCurrentAllocatedLocalWorker.pass, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩

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

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem paths_of_typed (lib : Library) {values : List Node}
    (typed : ∀ value ∈ values, Annotated (Origin lib) value) :
    ∀ path, ForestPath (Origin lib) path values := by
  intro path
  cases path with
  | nil => exact typed
  | cons index path =>
      intro value found
      exact .annotated path value (typed value (SourceEqualityProjectionGraph.select_member found))

section Source
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before after : Checked width}
variable {g s r e p h m c n budget : Nat} {values results : List Node}
variable {fourth savedFourth : Fourth} {memo saved : Memo}

/-- Literal class work retains complete annotations on every Type operand. -/
theorem classes {records : List Record}
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (ready : Ready lib (initial before memo))
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (typed : ∀ value ∈ values, Annotated (Origin lib) value)
    (ranges : SourceCurrentConjunctionScanClassPass.Ranges budget records values
      (prefixState before loaded inherited) fourth memo)
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ value ∈ results, Annotated (Origin lib) value := by
  have entry := prefix_ready lib receipt ready
  have operationGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked entry.checked.good) entry.checked.semantic entry.costs
  have finalGuards := SourceCurrentParentGuardHeapReturns.classes (Origin lib) actual
    operationGood entry.physicalMemo available guards
  obtain ⟨⟨outcome, kept⟩, scanned, scanFourth, warm, first, later⟩ := bind_done _ _ actual
  obtain ⟨scanRun, sameMemo⟩ := scan_done first
  subst warm
  obtain ⟨scanGraph, retained, checked, costs, extension, _scanGuards, known⟩ :=
    SourceSynthesisNativeTypeRecordScanWorker.scan lib formulas solver scanRun entry.checked entry.costs
      available closed (fun _ _ path _ => paths_of_typed lib typed (path.map Int.ofNat)) guards ranges.scan
  have scannedReady := scanned_ready lib entry checked costs extension
  cases outcome with
  | some stopped =>
      change SourceCurrentAllocatedLocalWorker.Outcome.done (EqualityLeafProjectionRuntimeEmpty.erase values)
        scanned scanFourth memo = .done results after savedFourth saved at later
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj later
      subst results
      subst after
      subst savedFourth
      subst saved
      obtain ⟨returned, resultClosed, routes⟩ := erased (Origin lib) values scanned.native.machine.heap
      exact ⟨scannedReady, receipt.extension.trans extension, returned, resultClosed, finalGuards, routes []⟩
  | none =>
      change (SourceCurrentAllocatedLocalWorker.required r h
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned scanFourth memo).bind
          (fun middle state next current => SourceCurrentAllocatedLocalWorker.pass e p h m c n kept middle state next current) =
            .done results after savedFourth saved at later
      obtain ⟨middle, state, next, current, requiredLocal, passed⟩ := bind_done _ _ later
      obtain ⟨heap, required, sameState, sameFourth, sameMemo⟩ := required_done requiredLocal
      subst state
      subst next
      subst current
      obtain ⟨passRun, sameFourth⟩ := pass_done passed
      subst savedFourth
      cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) with
      | node entries =>
          obtain ⟨nextReady, requiredExtension, middleAvailable, middleClosed, _, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun _ => False)
              (before := initial scanned memo) required compiled scannedReady known closed
              (fun index value found _ => typed value (List.mem_of_getElem? found))
              (fun _ _ _ assigned => False.elim assigned) (fun _ _ _ assigned => False.elim assigned)
          have middleTyped : ∀ value ∈ middle, Annotated (Origin lib) value := by
            intro value member
            obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
            exact (slots index value found).2 (by simp)
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs nextReady.physicalMemo nextReady.typedMemo
          have coherent := SourceSynthesisActualSelectedProgramFootprints.selected_regions receipt scanRun
            (fun _ => True) (fun _ _ => True.intro)
          obtain ⟨passGraph, _, _, _, _, _⟩ := SourceSynthesisNativeTypeClassWorker.pass lib e p h m c n
            classReady middleAvailable middleClosed (fun record member => (coherent record member).1)
            (fun _ _ path _ => paths_of_typed lib middleTyped (path.map Int.ofNat))
            (ranges.pass scanGraph kept retained r h middle heap required) passRun
          obtain ⟨finalReady, last, returned, resultClosed, routes⟩ :=
            SourceSynthesisNativeTypeClassPass.pass lib passGraph classReady middleAvailable middleClosed
              (fun record member => (coherent record member).1)
              (fun _ _ path _ => paths_of_typed lib middleTyped (path.map Int.ofNat))
          exact ⟨finalReady, receipt.extension.trans (extension.trans (requiredExtension.trans last)),
            returned, resultClosed, finalGuards, routes [] middleTyped⟩

/-- Every actual precheck branch retains a completely annotated Type forest. -/
theorem reduce {branch : SourceEqualityPrecheck.Branch}
    (receipt : Receipt formulas solver inventory guard loaded inherited before own branch)
    (ready : Ready lib (initial before memo))
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (typed : ∀ value ∈ values, Annotated (Origin lib) value)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo)
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
      values before fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧
      ∀ value ∈ results, Annotated (Origin lib) value := by
  cases branch with
  | classes records =>
      have continuation : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
          (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved := by
        simpa only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual, SourceCurrentAllocatedPrecheck.state] using actual
      exact classes lib formulas solver receipt ready available closed guards typed (ranges records receipt.actual) continuation
  | unchanged =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, routes, _⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.unchanged lib g s r e p h m c n budget fourth
          receipt ready available closed guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ :=
        SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards, routes [] typed⟩
  | emptyChildren =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, routes, _⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.emptyChildren lib g s r e p h m c n budget fourth receipt ready guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ :=
        SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards, routes [] typed⟩
end Source
end MicroCFTA.SourceSynthesisNativeTypeAnnotatedLocalWorker
