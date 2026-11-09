import MicroCFTA.SourceCurrentSharedScanInitialRanges
import MicroCFTA.SourceCurrentClassPassInitialRanges
import MicroCFTA.SourceCurrentSharedParentAlphabetReservation
import MicroCFTA.SourceCurrentAllocatedSharedRecordScanWorkerStability

/-!
# Shared Parent range plans from current uniform reservations

Literal shared Scan bounds retain checks before every reached native query.
Each actual completed preparation has the same checked intermediate state
as its numeric receipt. That receipt supplies the class edit ranges.
The proof does not reindex canonical Parent reads to observed bounds.
No successful Parent or future range supplier is an input.
-/
namespace MicroCFTA.SourceCurrentSharedParentUniformRanges
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceEqualityClassOrder (Record Coherent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "recordScan" => SourceCurrentAllocatedSharedRecordScanWorker.scan
variable {bits width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Literal Scan and Required prefixes retain checks at their actual states. -/
structure ClassesRanges (budget : Nat) (records : List Record) (values : List Node)
    (before : Checked width) (fourth : Fourth) (memo : Memo) : Prop where
  scan : ∀ g s p h n, SourceCurrentSharedScanInitialRanges.Ranges g s p h n budget values records before fourth
  pass : ∀ {g s p h n kept middle saved},
    recordScan g s p h n budget values records before fourth = .done (none, kept) middle saved →
    ∀ fuel readFuel results heap,
      SourceEqualityRequiredExecution.requireAll fuel readFuel
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle.native.machine.heap = .done results heap →
      SourceCurrentAllocatedClassPass.Ranges kept results (SourceCurrentConjunctionClassScan.advanceHeap middle heap) memo

/-- A literal live precheck selects its own shared class range plan. -/
def LocalRanges (budget : Nat) (loaded : Allocated) (inherited : EqValue) (values : List Node)
    (before : Checked width) (fourth : Fourth) (memo : Memo) : Prop :=
  ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
    ClassesRanges budget records values (prefixState before loaded inherited) fourth memo

/-- A live resident Parent checks its actual loaded field at every lower bound. -/
def ResidentRanges (budget : Nat) (request : Request) (before : Caller width) : Prop :=
  SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
    ∀ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
        .ok (some loaded) →
      LocalRanges budget loaded request.inherited request.value.children before.checked before.fourth before.merge

private theorem preparation_unique
    {budget : Nat} {records : List Record} {values firstValues secondValues : List Node}
    {before firstAfter secondAfter : Checked width} {fourth firstSaved secondSaved : Fourth}
    {first second : Option Class} {kept other : List Record}
    (one : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth
      first kept firstValues firstAfter firstSaved)
    (two : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth
      second other secondValues secondAfter secondSaved) :
    first = second ∧ kept = other ∧ firstValues = secondValues ∧ firstAfter = secondAfter ∧ firstSaved = secondSaved := by
  cases one with
  | stopped firstScan =>
      cases two with
      | stopped secondScan =>
          obtain ⟨same, rfl, rfl⟩ := SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique firstScan secondScan
          exact ⟨(Prod.mk.inj same).1, (Prod.mk.inj same).2, rfl, rfl, rfl⟩
      | prepared secondScan secondRequired =>
          have impossible := congrArg Prod.fst
            (SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique firstScan secondScan).1
          cases impossible
  | prepared firstScan firstRequired =>
      cases two with
      | stopped secondScan =>
          have impossible := congrArg Prod.fst
            (SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique firstScan secondScan).1
          cases impossible
      | prepared secondScan secondRequired =>
          obtain ⟨same, rfl, rfl⟩ := SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique firstScan secondScan
          obtain ⟨_, rfl⟩ := Prod.mk.inj same
          obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.requireAll_done_unique firstRequired secondRequired
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Current resources derive checks for every literal shared class prefix. -/
theorem classes_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List Node) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentSharedClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile) :
    ClassesRanges budget records values before.checked before.fourth before.merge := by
  have scans := SourceCurrentSharedScanInitialRanges.initial_ranges formulas solver inventory
    (guards before.checked.native.machine.heap) budget values records before memos initial frame profile fits available
    proper reserved.1 (SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
      initial.ready.semantic.ready.semantic.1.normal.facts)
  refine ⟨scans, ?_⟩
  intro g s p h n chosen after savedFourth actual r read results heap required
  obtain ⟨outcome, kept, prepared, middle, saved, next, current, receipt⟩ :=
    SourceCurrentSharedScanRequiredNumeric.complete formulas solver inventory budget values records before memos
      initial frame profile fits available proper coherent active reserved.1
  have given : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before.checked before.fourth
      none chosen results (SourceCurrentConjunctionClassScan.advanceHeap after heap) savedFourth :=
    .prepared actual required
  have aligned := preparation_unique receipt.actual given
  have room : SourceCurrentConstrainedCapClassForecast.Reserved bits kept prepared.length
      (SourceCurrentSharedScanRequiredForecast.finalProfile budget values.length records
        (guards before.checked.native.machine.heap) profile) := by
    simpa only [receipt.length] using SourceCurrentSharedClassesForecast.class_reserved receipt.selected bits budget
      values.length (guards before.checked.native.machine.heap) profile reserved
  have plan := SourceCurrentClassPassInitialRanges.pass_ranges formulas solver next kept
    (fun record member => coherent record (receipt.selected.subset member))
    (fun record member => active record (receipt.selected.subset member))
    prepared middle before.merge
    (SourceCurrentSharedScanRequiredForecast.finalProfile budget values.length records
      (guards before.checked.native.machine.heap) profile)
    receipt.frame receipt.fits receipt.available (receipt.domains aligned.1)
    receipt.post.context.stored receipt.post.context.covered current receipt.post.context.globals room
  simpa only [aligned.2.1, aligned.2.2.1, aligned.2.2.2.1] using plan

private theorem loaded_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (reserved : SourceCurrentSharedLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile) :
    LocalRanges budget loaded inherited values before.checked before.fourth before.merge := by
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked initial.ready initial.admitted original cached loaded found inherited inheritedReady
  intro records actual
  have same := Except.ok.inj (checked.actual.symm.trans actual)
  cases same
  have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
    ⟨checked.ready, checked.admitted, frame.context, frame.joint, frame.origins⟩
  have prefixFits : Fits profile (prefixState before.checked loaded inherited) :=
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩
  have prefixPost : Post formulas solver inventory before
      (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos :=
    ⟨⟨checked.ready, checked.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge checked.effects,
      initial.stored, initial.covered, initial.correct, initial.globals, initial.probes⟩,
      checked.effects, extends_refl _, fun _ _ present => present⟩
  obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
  have room : SourceCurrentSharedClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile := by
    simpa only [SourceCurrentSharedLocalForecast.Reserved, checked.actual] using reserved
  exact classes_ranges formulas solver inventory budget values records
    (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos
    prefixPost.context prefixFrame profile prefixFits available
    (fun record member => proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩))
    (fun record member => (fields record member).1) (fun record member => (fields record member).2.2) room

/-- Initial resident data and its finite uniform reservation derive every reached Parent range plan. -/
theorem resident_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentSharedParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    ResidentRanges budget request before := by
  have reserved := SourceCurrentSharedParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet
    request before memos initial profile fits known inherited resident uniform
  intro live loaded found
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have room : SourceCurrentSharedLocalForecast.Reserved bits budget request.value.children.length loaded request.inherited
      before.checked profile := by
    simpa only [SourceCurrentSharedParentForecast.residentReserved, SourceCurrentSharedParentForecast.Reserved,
      live, Bool.false_eq_true, ite_false, found] using reserved
  exact loaded_ranges formulas solver inventory budget request.value.entry.key.constraint loaded request.inherited
    request.value.children before memos initial frame profile fits cached found inherited
    (initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident) room


end MicroCFTA.SourceCurrentSharedParentUniformRanges
