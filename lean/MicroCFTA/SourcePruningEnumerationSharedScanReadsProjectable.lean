import MicroCFTA.SourcePruningEnumerationParentProjectionTargets
import MicroCFTA.SourceCurrentAllocatedTargetObserved
import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Projectable heaps through the actual shared scan reads

The observed read graph retains each gate, seeded query, and shared call.
Actual completed native traces supply their own word checks.
Current heap facts pass through the same checked states and memo snapshots.
A stopped scan retains its actual reached state and skips its suffix.
This component observes completed scan reads. It does not prove completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedScanReadsProjectable
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "PhysicalHeap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Projected" =>
  (fun guard : Guard => SourcePruningEnumerationConstraint.project guard ≠ none)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap Projected
local notation "Supported" => SourceEqualityAnnotationHeap.Heap
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Source equality support is exactly successful projection, including residual guards. -/
private theorem supported_iff (guard : Guard) :
    (∃ classes, SourceCompactGuards.sourceEqualities guard = some classes) ↔ Projected guard := by
  cases found : SourceCompactGuards.sourceEqualities guard <;>
    simp [SourcePruningEnumerationConstraint.project, found]

omit [DecidableEq Node] in
/-- An actual completed fold supplies each range check at its own unique prefixes. -/
private theorem fold_ranges_of_actual
    {values : List Node} {paths : List (List Int)} {before after : Checked width} {result : Node}
    (actual : Fold values paths before result after) : FoldRanges values paths before := by
  induction actual with
  | one operand => exact .one
  | cons operand rest native ih =>
      refine .cons ?_ ?_
      · intro value middle first
        obtain ⟨rfl, rfl⟩ := Operand.unique operand first
        exact ih
      · intro value middle tail later first remaining
        obtain ⟨rfl, rfl⟩ := Operand.unique operand first
        obtain ⟨rfl, rfl⟩ := Fold.unique rest remaining
        exact SourceCurrentAllocatedNativeObservedWords.trace_wordRanges native

omit [DecidableEq Node] in
/-- The actual first-seed rotation supplies its own reached range plan. -/
private theorem seeded_ranges_of_actual
    {values : List Node} {paths : List (List Int)} {before after : Checked width} {result : Node}
    (actual : Seeded values paths before result after) : SeededRanges values paths before := by
  cases actual with
  | nil => trivial
  | nonempty fold => exact fold_ranges_of_actual fold

omit [DecidableEq Node] in
/-- An actual primary read retains the current forest and physical guard support. -/
private theorem primary_read_heap
    {values : List Node} {paths : EqualityNormalize.Class} {before : Checked width}
    {answer : Bool} {heap : PhysicalHeap} {memos saved : Memos}
    {actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths
      before.native.machine.heap answer heap}
    (_reads : SourceCurrentAllocatedPrimaryReads.ClassReads actual memos saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (current : Heap before.native.machine.heap) :
    Ready (advanceHeap before heap) ∧ Values heap values ∧ Heap heap := by
  have checked := SourceCurrentConjunctionClassScan.primary_effects source reaches actual ready available
  have fields := SourcePrimaryGateEffects.class_effects Projected source reaches actual
    ready.semantic ready.costs available current
  exact ⟨checked.1, checked.2.2, fields.2.2.2⟩

omit [DecidableEq Node] in
/-- An actual secondary read retains the same checked update and original forest. -/
private theorem secondary_read_heap
    {values : List Node} {paths : EqualityNormalize.Class} {before : Checked width}
    {answer : Bool} {heap : PhysicalHeap} {memos saved : Memos}
    {actual : SourceCurrentSecondaryTrace.ClassTrace source values paths
      before.native.machine.heap answer heap}
    (_reads : SourceCurrentSecondaryMemos.ClassReads actual memos saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (current : Heap before.native.machine.heap) :
    Ready (advanceHeap before heap) ∧ Values heap values ∧ Heap heap := by
  have checked := SourceCurrentConjunctionClassScan.secondary_effects source actual ready available
  have fields := SourceCurrentSecondaryEffects.class_effects Projected source actual
    ready.semantic ready.costs available current
  exact ⟨checked.1, checked.2.2, fields.2.2.2⟩

omit [DecidableEq Node] in
/-- The actual false secondary return anchors the same completed seeded query. -/
private theorem seeded_read_heap
    {values : List Node} {paths : EqualityNormalize.Class} {before after : Checked width}
    {anchor : PhysicalHeap} {query : Node} {memos middle final : Memos}
    {secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths
      before.native.machine.heap false anchor}
    {seeded : Seeded values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query after}
    (secondRead : SourceCurrentSecondaryMemos.ClassReads secondary memos middle)
    (_seededRead : SourceCurrentAllocatedSeededMemos.SeededReads seeded middle final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ []) (current : Heap before.native.machine.heap) :
    Ready after ∧ Values after.native.machine.heap values ∧
      Available after.native.machine.heap query ∧ Heap after.native.machine.heap := by
  obtain ⟨nextReady, nextValues, nextHeap⟩ := secondary_read_heap secondRead ready available current
  obtain ⟨anchorSemantic, _anchorCosts, anchorReady, _kept, _values, _replay, supported⟩ :=
    SourceCurrentSecondarySeededSupport.class_support source secondary
      ready.semantic ready.costs available proper
  have ranges := seeded_ranges_of_actual seeded
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready _ nextReady.good
    nextReady.semantic nextReady.costs
  obtain ⟨good, effects, _extension, scopedCache, idle, resident, _closed⟩ :=
    SourceCurrentAllocatedSeededQuery.Seeded.effects source anchor anchorSemantic anchorReady seeded ranges
      nextReady.good physicalReady nextReady.scopedCache nextReady.idle nextValues
      (InternedConstructorTemplates.grows_refl _) supported
  have fields := SourcePruningEnumerationSeededProjectionHeap.seeded_heap source anchor
    anchorSemantic anchorReady seeded ranges nextReady.good physicalReady nextReady.scopedCache nextReady.idle
      nextValues (InternedConstructorTemplates.grows_refl _) supported nextHeap
  exact ⟨⟨good, effects.ready.semantic, effects.ready.costs, scopedCache, idle⟩,
    fun value member => effects.keeps.available value (nextValues value member), resident, fields⟩

/-- The actual shared call retains its literal snapshot, including a true stop. -/
private theorem checked_call_heap
    {p h budget : Nat} {values : List Node} {query : Node} {before after : Checked width}
    {memo saved : Memo} {answer : Bool} {snapshot : Snapshot}
    (actual : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget query before memo =
      .done answer after saved snapshot)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (queryAvailable : Available before.native.machine.heap query) (current : Heap before.native.machine.heap) :
    Ready after ∧ Values after.native.machine.heap values ∧ Heap after.native.machine.heap := by
  obtain ⟨raw, advanced⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done actual
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  have effects := (SourceCurrentConjunctionSharedWorkerEffects.call_effects
    p h budget memo query (physical before) physicalReady queryAvailable).1
  have fields := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap Projected
    p h budget memo query (physical before) physicalReady current queryAvailable
  rw [raw] at effects fields
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at effects fields
  rw [advanced]
  refine ⟨SourceCurrentConjunctionClassScan.advance_ready before snapshot.storage.requirements.physical ready effects,
    ?_, ?_⟩
  · intro value member
    exact effects.keeps.available value (available value member)
  · change Heap (physical (advancePhysical before snapshot.storage.requirements.physical)).heap
    rw [SourceCurrentAllocatedQueryMemo.physical_advance]
    exact fields

/-- The same shared read prefix transports current readiness, originals, and guard support. -/
private theorem scan_projection_heap
    {budget : Nat} {values : List Node} {records kept : List Record} {before after : Checked width}
    {memo saved : Memo} {outcome : Option EqualityNormalize.Class} {memos final : Memos}
    (reads : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before memo
      outcome kept after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (current : Heap before.native.machine.heap) :
    Ready after ∧ Values after.native.machine.heap values ∧ Heap after.native.machine.heap := by
  revert ready available proper current
  induction reads with
  | nil => intro ready available _ current; exact ⟨ready, available, current⟩
  | selected first tail ih =>
      intro ready available proper current
      obtain ⟨checked, values, fields⟩ := primary_read_heap first ready available current
      exact ih checked values (fun record member => proper record (List.mem_cons_of_mem _ member)) fields
  | skipped first second tail ih =>
      intro ready available proper current
      obtain ⟨checked, values, fields⟩ := primary_read_heap first ready available current
      obtain ⟨later, laterValues, laterFields⟩ := secondary_read_heap second checked values fields
      exact ih later laterValues (fun record member => proper record (List.mem_cons_of_mem _ member)) laterFields
  | continued first second seeded called _callRead tail ih =>
      intro ready available proper current
      obtain ⟨checked, values, fields⟩ := primary_read_heap first ready available current
      obtain ⟨queryReady, queryValues, queryAvailable, queryFields⟩ :=
        seeded_read_heap second seeded checked values (proper _ List.mem_cons_self) fields
      obtain ⟨later, laterValues, laterFields⟩ :=
        checked_call_heap called queryReady queryValues queryAvailable queryFields
      exact ih later laterValues (fun record member => proper record (List.mem_cons_of_mem _ member)) laterFields
  | stopped first second seeded called _callRead =>
      intro ready available proper current
      obtain ⟨checked, values, fields⟩ := primary_read_heap first ready available current
      obtain ⟨queryReady, queryValues, queryAvailable, queryFields⟩ :=
        seeded_read_heap second seeded checked values (proper _ List.mem_cons_self) fields
      exact checked_call_heap called queryReady queryValues queryAvailable queryFields

/-- Actual shared scan reads preserve support at their exact continued or stopped endpoint. -/
theorem scan_reads_projectable
    {budget : Nat} {values : List Node} {records kept : List Record} {before after : Checked width}
    {memo saved : Memo} {outcome : Option EqualityNormalize.Class} {memos final : Memos}
    (reads : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before memo
      outcome kept after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (current : Supported before.native.machine.heap) :
    Ready after ∧ Values after.native.machine.heap values ∧ Supported after.native.machine.heap := by
  have projected : Heap before.native.machine.heap := by
    intro key edge found
    exact (supported_iff _).mp (current key edge found)
  obtain ⟨checked, values, fields⟩ := scan_projection_heap reads ready available proper projected
  refine ⟨checked, values, ?_⟩
  intro key edge found
  exact (supported_iff _).mpr (fields key edge found)

end MicroCFTA.SourcePruningEnumerationSharedScanReadsProjectable
