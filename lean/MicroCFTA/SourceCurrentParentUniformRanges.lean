import MicroCFTA.SourceCurrentParentUniformEnvelope
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual
import MicroCFTA.SourceCurrentEditListNumericRanges

/-!
# Parent range plans from initial uniform reservations

The initial numeric receipts construct each earlier Scan, Required, and
class-fold prefix. Execution uniqueness identifies every completed prefix
in the range plan with that constructed prefix. No successful Parent call
or future caller invariant is an input.
-/
namespace MicroCFTA.SourceCurrentParentUniformRanges
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedClassEditPlan
open SourceEqualityClassOrder (Record Coherent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
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
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {bits width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem class_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (coherent : Coherent record) (active : Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (room : Room bits (SourceCurrentConstrainedCapClassForecast.classProfile record values.length profile)) :
    SourceCurrentAllocatedClassEdits.ClassRanges record values before memo := by
  have ready := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
    before.native.machine.heap before memo frame.ready frame.admitted
    (SourceEqualityRequiredCache.pure_keeps _ frame.ready.semantic.ready) physical covered
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  have reserved : SourceCurrentEditListNumeric.Reserved bits record values.length
      (compiled record) values.length profile :=
    SourceCurrentConstrainedCapClassForecast.class_reserved bits record values.length profile room
  exact SourceCurrentEditListNumericRanges.list_ranges formulas solver inventory record values
    before.native.machine.heap (SourceCurrentAllocatedSharedTargetState.initial before memo) profile
    ready frame fits available domains coherent active (compiled record) (compiled_populated record)
    (compiled_allowed record) values available safe memos valid reserved

private theorem fold_unique {records values first second}
    {before after later : Checked width} {memo saved current : Memo}
    (one : SourceCurrentAllocatedClassPass.Fold records values before memo first after saved)
    (two : SourceCurrentAllocatedClassPass.Fold records values before memo second later current) :
    first = second ∧ after = later ∧ saved = current := by
  obtain ⟨e, p, h, m, s, n, completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete one
  obtain ⟨E, P, H, M, S, N, other⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete two
  exact SourceCurrentAllocatedClassWorkerStability.fold_done_unique
    (completed e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (other E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

private theorem pass_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List Record)
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile) :
    SourceCurrentAllocatedClassPass.Ranges records values before memo := by
  induction records generalizing inventory values before memo profile memos with
  | nil => exact .nil
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
      have tailRoom := SourceCurrentConstrainedCapClassForecast.reserved_tail bits record records values.length profile reserved
      refine .cons (ih inventory tailCoherent tailActive values before memo profile frame fits available
        tailDomains physical covered memos valid tailRoom) ?_
      intro supplied step current actualTail
      obtain ⟨middle, next, saved, tailInventory, final, chosen, _reads, receipt, returned, numeric,
          sameLength, _done, _stable⟩ :=
        SourceCurrentClassPassNumeric.fold formulas solver inventory records tailCoherent tailActive values
          before memo profile frame fits available tailDomains physical covered memos valid tailRoom
      obtain ⟨rfl, rfl, rfl⟩ := fold_unique chosen actualTail
      have room : Room bits (SourceCurrentConstrainedCapClassForecast.classProfile record middle.length
          (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile)) := by
        simpa only [sameLength] using
          SourceCurrentConstrainedCapClassForecast.reserved_head bits record records values.length profile reserved
      exact class_ranges formulas solver tailInventory record (coherent _ List.mem_cons_self)
        (active _ List.mem_cons_self) middle next saved
        (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile)
        returned numeric receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered final receipt.globals.valid room

variable [DecidableEq (Value Symbol Guard)]

private theorem retained_unique
    {budget : Nat} {values : List (Value Symbol Guard)} {records kept other : List Record}
    {first second : Option Class} {selected chosen : Constraints}
    {before after later : Checked width} {memo saved current : Fourth}
    {one : SourceCurrentConjunctionClassScan.Scan budget source reaches values (records.map Record.paths)
      before memo first selected after saved}
    {two : SourceCurrentConjunctionClassScan.Scan budget source reaches values (records.map Record.paths)
      before memo second chosen later current}
    (left : SourceCurrentConjunctionSelectedRecords.Retained one records kept)
    (right : SourceCurrentConjunctionSelectedRecords.Retained two records other) :
    (first, kept) = (second, other) ∧ after = later ∧ saved = current := by
  obtain ⟨g, s, p, h, n, completed⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete left
  obtain ⟨G, S, P, H, N, other⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete right
  exact SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique
    (completed g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (other G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

private theorem preparation_unique
    {budget : Nat} {records : List Record} {values firstValues secondValues : List (Value Symbol Guard)}
    {before firstAfter secondAfter : Checked width} {fourth firstSaved secondSaved : Fourth}
    {first second : Option Class} {kept other : List Record}
    (one : SourceCurrentScanRequiredNumeric.Execution budget records values before fourth
      first kept firstValues firstAfter firstSaved)
    (two : SourceCurrentScanRequiredNumeric.Execution budget records values before fourth
      second other secondValues secondAfter secondSaved) :
    first = second ∧ kept = other ∧ firstValues = secondValues ∧ firstAfter = secondAfter ∧ firstSaved = secondSaved := by
  cases one with
  | stopped firstScan firstRetained =>
      cases two with
      | stopped secondScan secondRetained =>
          obtain ⟨same, rfl, rfl⟩ := retained_unique firstRetained secondRetained
          exact ⟨(Prod.mk.inj same).1, (Prod.mk.inj same).2, rfl, rfl, rfl⟩
      | prepared secondScan secondRetained secondRequired =>
          have impossible := congrArg Prod.fst (retained_unique firstRetained secondRetained).1
          cases impossible
  | prepared firstScan firstRetained firstRequired =>
      cases two with
      | stopped secondScan secondRetained =>
          have impossible := congrArg Prod.fst (retained_unique firstRetained secondRetained).1
          cases impossible
      | prepared secondScan secondRetained secondRequired =>
          obtain ⟨same, rfl, rfl⟩ := retained_unique firstRetained secondRetained
          obtain ⟨_, rfl⟩ := Prod.mk.inj same
          obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.requireAll_done_unique firstRequired secondRequired
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem classes_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile) :
    SourceCurrentConjunctionScanClassPass.Ranges budget records values before.checked before.fourth before.merge := by
  obtain ⟨outcome, kept, prepared, middle, saved, next, current, receipt⟩ :=
    SourceCurrentScanRequiredNumeric.complete formulas solver inventory budget values records before memos
      initial frame profile fits available proper coherent active reserved.1
  refine ⟨receipt.ranges, ?_⟩
  intro selected after savedFourth actual chosen retained r h results heap required
  have samePaths := retained.fields.2
  cases samePaths
  have given : SourceCurrentScanRequiredNumeric.Execution budget records values before.checked before.fourth
      none chosen results (SourceCurrentConjunctionClassScan.advanceHeap after heap) savedFourth :=
    .prepared actual retained required
  have aligned := preparation_unique receipt.actual given
  have room : SourceCurrentConstrainedCapClassForecast.Reserved bits kept prepared.length
      (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
        (guards before.checked.native.machine.heap) profile) := by
    simpa only [receipt.length] using SourceCurrentClassesForecast.class_reserved receipt.selected bits budget
      values.length (guards before.checked.native.machine.heap) profile reserved
  have plan := pass_ranges formulas solver next kept
    (fun record member => coherent record (receipt.selected.subset member))
    (fun record member => active record (receipt.selected.subset member))
    prepared middle before.merge
    (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
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
    (reserved : SourceCurrentLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before.checked before.fourth before.merge := by
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
  have room : SourceCurrentClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile := by
    simpa only [SourceCurrentLocalForecast.Reserved, checked.actual] using reserved
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
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := by
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet
    request before memos initial profile fits known inherited resident uniform
  intro live loaded found
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  have room : SourceCurrentLocalForecast.Reserved bits budget request.value.children.length loaded request.inherited
      before.checked profile := by
    simpa only [SourceCurrentParentForecast.residentReserved, SourceCurrentParentForecast.Reserved,
      live, Bool.false_eq_true, ite_false, found] using reserved
  exact loaded_ranges formulas solver inventory budget request.value.entry.key.constraint loaded request.inherited
    request.value.children before memos initial frame profile fits cached found inherited
    (initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident) room

end MicroCFTA.SourceCurrentParentUniformRanges
