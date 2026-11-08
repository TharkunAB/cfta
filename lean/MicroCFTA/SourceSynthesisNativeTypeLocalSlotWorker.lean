import MicroCFTA.SourceSynthesisNativeTypeLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeClassSlotFields

/-!
# All mixed slots at actual local class returns

The original source occurrence supplies each selected Program footprint.
Required classifies every returned slot. The actual class pass retains
those classifications at its own checked state and warm Merge table.
Stopped scans return literal Empty slots. The earlier local theorem
supplies readiness, guard profiles and source endpoint routes unchanged.
These local results do not classify every nested or reached worker input.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeLocalSlotWorker
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

private theorem erased_slots (valid : Guard → Prop) (assigned : Nat → Prop) (values : List Node) :
    ∀ index value, (EqualityLeafProjectionRuntimeEmpty.erase values)[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value found
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? found)
  exact ⟨fun _ => .empty, fun _ => .empty⟩

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

section Source
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before after : Checked width}
variable {records : List Record} {g s r e p h m c n budget : Nat} {values results : List Node}
variable {fourth savedFourth : Fourth} {memo saved : Memo}
variable (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
variable (ready : Ready lib (initial before memo))
variable (available : Values before.native.machine.heap values) (closed : ClosedValues values)
variable (guards : GuardHeap (Origin lib) before.native.machine.heap)
variable (ranges : SourceCurrentConjunctionScanClassPass.Ranges budget records values
  (prefixState before loaded inherited) fourth memo)

section Application
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value)
include occurrence receipt ready available closed typed fields guards ranges

/-- Actual application class reduction retains every mixed returned slot. -/
theorem application_classes
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        ((index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  obtain ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes⟩ :=
    SourceSynthesisNativeTypeLocalWorker.application_classes
      (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
      (available := available) (closed := closed) (guards := guards) (ranges := ranges)
      (types := types) (function := function) (argument := argument) (sourceName := sourceName)
      (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) actual
  refine ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes, ?_⟩
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.applicationRegion
    (SourceSynthesisGuardRegions.application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fields index value found) (typed index value found)
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.application_paths (Origin lib) (fun index => index = 2 ∨ index = 3)
      values (by decide) inputSlots path ((original record member).2 path included)
  obtain ⟨⟨outcome, kept⟩, scanned, scanFourth, warm, first, later⟩ := bind_done _ _ actual
  obtain ⟨scanRun, sameMemo⟩ := scan_done first
  subst warm
  obtain ⟨scanGraph, retained, checked, costs, scanExtension, _scanGuards, known⟩ :=
    SourceSynthesisNativeTypeRecordScanWorker.scan lib formulas solver scanRun entry.checked entry.costs
      available closed recordPaths guards ranges.scan
  have scannedReady := scanned_ready lib entry checked costs scanExtension
  cases outcome with
  | some stopped =>
      change SourceCurrentAllocatedLocalWorker.Outcome.done (EqualityLeafProjectionRuntimeEmpty.erase values)
        scanned scanFourth memo = .done results after savedFourth saved at later
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj later
      subst results
      exact erased_slots (Origin lib) (fun index => index = 2 ∨ index = 3) values
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
          have only : ∀ (index : Nat) children,
              SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
              (index = 2 ∨ index = 3) → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
            intro index children found assigned
            exact SourceSynthesisActualSelectedProgramFootprints.application_annotation_only types function argument
              sourceName sourceChildren occurrence receipt scanRun compiled index assigned found
          obtain ⟨nextReady, _, middleAvailable, middleClosed, _, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 2 ∨ index = 3)
              (before := initial scanned memo) required compiled scannedReady known closed typed fields only
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs nextReady.physicalMemo nextReady.typedMemo
          obtain ⟨_, _, selected⟩ := SourceSynthesisTypeRequiredRoutes.application_requireAll (Origin lib)
            types function argument sourceName sourceChildren occurrence receipt scanRun required checked.semantic costs
            known closed checked.stored.constructors typed fields
          have coherent := fun record member => (selected record member).1
          have paths := fun record member => (selected record member).2
          obtain ⟨passGraph, _⟩ := SourceSynthesisNativeTypeClassWorker.pass lib e p h m c n
            classReady middleAvailable middleClosed coherent paths
            (ranges.pass scanGraph kept retained r h middle heap required) passRun
          apply SourceSynthesisNativeTypeClassSlotFields.pass_slots lib (fun index => index = 2 ∨ index = 3)
            passGraph classReady middleAvailable middleClosed coherent paths
          · intro record member index assigned
            exact (SourceSynthesisActualSelectedProgramFootprints.application_footprint types function argument
              sourceName sourceChildren occurrence receipt scanRun member index assigned).2 1 (by decide)
          · exact fun index value found => (slots index value found).2
          · exact fun index value found => (slots index value found).1

/-- The actual application reduce's classes branch retains all mixed slots. -/
theorem application_reduce
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
      values before fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        ((index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  have continuation : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved := by
    simpa only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual, SourceCurrentAllocatedPrecheck.state] using actual
  exact application_classes (lib := lib) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards) (ranges := ranges)
    (types := types) (function := function) (argument := argument) (sourceName := sourceName)
    (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) continuation
end Application

section Filter
variable (candidates goal : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
variable (typed : ∀ index value, values[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
variable (fields : ∀ index value, values[index]? = some value → index = 1 → AnnotationFields (Origin lib) value)
include occurrence receipt ready available closed typed fields guards ranges

/-- Actual filter class reduction retains every mixed returned slot. -/
theorem filter_classes
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        (index = 1 → AnnotationFields (Origin lib) value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  obtain ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes⟩ :=
    SourceSynthesisNativeTypeLocalWorker.filter_classes
      (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
      (available := available) (closed := closed) (guards := guards) (ranges := ranges)
      (candidates := candidates) (goal := goal) (sourceName := sourceName) (sourceChildren := sourceChildren)
      (occurrence := occurrence) (typed := typed) (fields := fields) actual
  refine ⟨finalReady, extension, returned, resultClosed, finalGuards, guardRoutes, ?_⟩
  have entry := prefix_ready lib receipt ready
  have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions receipt
    SourceSynthesisGuardRegions.filterRegion
    (SourceSynthesisGuardRegions.filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2
  have inputSlots := fun index value found => And.intro (fields index value found) (typed index value found)
  have recordPaths := fun record member path included =>
    SourceSynthesisTypeRequiredRoutes.filter_paths (Origin lib) (fun index => index = 1)
      values (by decide) inputSlots path ((original record member).2 path included)
  obtain ⟨⟨outcome, kept⟩, scanned, scanFourth, warm, first, later⟩ := bind_done _ _ actual
  obtain ⟨scanRun, sameMemo⟩ := scan_done first
  subst warm
  obtain ⟨scanGraph, retained, checked, costs, scanExtension, _scanGuards, known⟩ :=
    SourceSynthesisNativeTypeRecordScanWorker.scan lib formulas solver scanRun entry.checked entry.costs
      available closed recordPaths guards ranges.scan
  have scannedReady := scanned_ready lib entry checked costs scanExtension
  cases outcome with
  | some stopped =>
      change SourceCurrentAllocatedLocalWorker.Outcome.done (EqualityLeafProjectionRuntimeEmpty.erase values)
        scanned scanFourth memo = .done results after savedFourth saved at later
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj later
      subst results
      exact erased_slots (Origin lib) (fun index => index = 1) values
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
          have only : ∀ (index : Nat) children,
              SourceEqualityNeededMap.lookup (index : Int) entries = some (.node children) →
              index = 1 → SourceCurrentHereditaryProgramRequired.AnnotationOnly children := by
            intro index children found assigned
            subst index
            exact SourceSynthesisActualSelectedProgramFootprints.filter_annotation_only candidates goal
              sourceName sourceChildren occurrence receipt scanRun compiled found
          obtain ⟨nextReady, _, middleAvailable, middleClosed, _, slots⟩ :=
            SourceSynthesisNativeTypeRequired.requireAll lib (fun index => index = 1)
              (before := initial scanned memo) required compiled scannedReady known closed typed fields only
          have classReady : Ready lib (initial (advanceHeap scanned heap) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ nextReady.checked nextReady.costs nextReady.physicalMemo nextReady.typedMemo
          obtain ⟨_, _, selected⟩ := SourceSynthesisTypeRequiredRoutes.filter_requireAll (Origin lib)
            candidates goal sourceName sourceChildren occurrence receipt scanRun required checked.semantic costs
            known closed checked.stored.constructors typed fields
          have coherent := fun record member => (selected record member).1
          have paths := fun record member => (selected record member).2
          obtain ⟨passGraph, _⟩ := SourceSynthesisNativeTypeClassWorker.pass lib e p h m c n
            classReady middleAvailable middleClosed coherent paths
            (ranges.pass scanGraph kept retained r h middle heap required) passRun
          apply SourceSynthesisNativeTypeClassSlotFields.pass_slots lib (fun index => index = 1)
            passGraph classReady middleAvailable middleClosed coherent paths
          · intro record member index assigned
            subst index
            exact (SourceSynthesisActualSelectedProgramFootprints.filter_footprint candidates goal
              sourceName sourceChildren occurrence receipt scanRun member).2 1 (by decide)
          · exact fun index value found => (slots index value found).2
          · exact fun index value found => (slots index value found).1

/-- The actual filter reduce's classes branch retains all mixed slots. -/
theorem filter_reduce
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
      values before fourth memo = .done results after savedFourth saved) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
        ForestPath (Origin lib) (path.map Int.ofNat) results) ∧
      ∀ index value, results[index]? = some value →
        (index = 1 → AnnotationFields (Origin lib) value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  have continuation : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      (prefixState before loaded inherited) fourth memo = .done results after savedFourth saved := by
    simpa only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual, SourceCurrentAllocatedPrecheck.state] using actual
  exact filter_classes (lib := lib) (formulas := formulas) (solver := solver)
    (receipt := receipt) (ready := ready) (available := available) (closed := closed) (guards := guards) (ranges := ranges)
    (candidates := candidates) (goal := goal) (sourceName := sourceName) (sourceChildren := sourceChildren)
    (occurrence := occurrence) (typed := typed) (fields := fields) continuation
end Filter
end Source
end MicroCFTA.SourceSynthesisNativeTypeLocalSlotWorker
