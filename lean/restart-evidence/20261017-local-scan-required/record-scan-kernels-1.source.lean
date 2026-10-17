import MicroCFTA.SourceCurrentRecordScanNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.RecordScanNumericKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected

private theorem initial_frame (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before (bits + 2)) :=
  Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl

private def values : List (Value Symbol Guard) := [value, value, .reference .depth]
private def classes : EqualityNormalize.Constraints := [[[7], [8]], [[7], [8]]]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1
  · exact (initial width).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [] := by
  intro paths member path included
  have same : paths = [[7], [8]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl <;> decide
private theorem active : ∀ paths ∈ classes, EqualityNormalize.Nontrivial paths := by
  intro paths member
  have same : paths = [[7], [8]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  exact ⟨[7], by simp, [8], by simp, by decide⟩
private theorem context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  have frame : Frame formulas solver inventory (before width) :=
    Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact ⟨(initial width).1, frame.admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver (before width)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
    SourceCurrentMemoMergeEffects.stored_empty heap,
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
      (SourceEqualityPCSGuard.holds formulas solver) ambient),
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap,
    SourceCurrentAllocatedMuRebuild.constructed expression value heap constructed⟩

private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩


private theorem initial_frame (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl


private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[7], [8]] with
  | some result => result
  | none => ⟨.empty, []⟩
private theorem record_built : SourceEqualityClassOrder.recordOf [[7], [8]] = some record := by cbv
private theorem record_paths : record.paths = [[7], [8]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨other, built, coherent, _paths⟩ := SourceEqualityClassOrder.recordOf_complete [[7], [8]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(7, .terminal), (8, .terminal)], by cbv⟩)
  have same : other = record := Option.some.inj (built.symm.trans record_built)
  exact same ▸ coherent
private def records := [record, record]
private theorem records_paths : records.map SourceEqualityClassOrder.Record.paths = classes := by
  simp only [records, List.map_cons, List.map_nil, record_paths, classes]
private theorem records_coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  have same : own = record := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ record_coherent
private theorem records_proper : ∀ own ∈ records, ∀ path ∈ own.paths, path ≠ [] := by
  intro own member
  exact proper own.paths (records_paths ▸ List.mem_map.mpr ⟨own, member, rfl⟩)
private theorem records_active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  exact active own.paths (records_paths ▸ List.mem_map.mpr ⟨own, member, rfl⟩)

private theorem reserved_of_room (bits budget count : Nat) (classes : EqualityNormalize.Constraints)
    (alphabet : List Guard) (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      (SourceCurrentScanNumericForecast.schedule budget count classes alphabet profile).2) :
    SourceCurrentScanNumericForecast.Reserved bits budget count classes alphabet profile := by
  induction classes generalizing alphabet profile with
  | nil => trivial
  | cons paths classes ih =>
      have firstRoom := room.mono
        (SourceCurrentScanNumericForecast.schedule_profile_ge budget count classes
          (SourceCurrentScanNumericForecast.classStep budget count paths alphabet profile).1
          (SourceCurrentScanNumericForecast.classStep budget count paths alphabet profile).2)
      have queryRoom := firstRoom.mono
        (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge
          (SourceCurrentSeededGuardForecast.finalAlphabet alphabet count (paths.map (List.map Int.ofNat))
            (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths profile)))
          budget (SourceCurrentConstrainedCapSeededForecast.finalProfile count (paths.map (List.map Int.ofNat))
            (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths profile))))
      refine ⟨?_, ih _ _ room⟩
      cases paths with
      | nil => trivial
      | cons seed rest =>
          exact SourceCurrentConstrainedCapSeededForecast.reserved_of_final_room bits count (seed.map Int.ofNat)
            (rest.map (List.map Int.ofNat)) _ queryRoom

private theorem missing_gate : EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values record.paths heap false heap := by
  rw [record_paths]
  exact .next (.child (.missing rfl)) (.next (.child (.missing rfl)) .nil)
private def expected (width : Nat) : SourceCurrentConjunctionClassScan.Scan 0 SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
    (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty
    none (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty := by
  exact .selected missing_gate (.selected missing_gate .nil)
private theorem expected_retained (width : Nat) :
    SourceCurrentConjunctionSelectedRecords.Retained (expected width) records records :=
  .selected rfl (.selected rfl .nil)

/-- An initial computed reservation constructs a full record Scan and keeps both identical source occurrences. -/
theorem constructed_duplicate_records
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ bits next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver
          (SourceCurrentConjunctionGuardUniverse.guards heap) profile 0 values
          (records.map SourceEqualityClassOrder.Record.paths) (before (bits + 2)) SourceCurrentEmptinessMemo.empty
          none (records.map SourceEqualityClassOrder.Record.paths) (before (bits + 2)) SourceCurrentEmptinessMemo.empty next,
        SourceCurrentConjunctionSelectedRecords.Retained receipt.actual records records ∧
        SourceCurrentAllocatedScanSourceReads.ScanReads receipt.actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
          (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) (before (bits + 2))
            SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty) final ∧
        records.length = 2 ∧
        ∀ g s p h n, SourceCurrentScanNumericForecast.fuel 0 values.length
            (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentConjunctionGuardUniverse.guards heap) profile ≤ g →
          SourceCurrentScanNumericForecast.fuel 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
            (SourceCurrentConjunctionGuardUniverse.guards heap) profile ≤ s →
          SourceCurrentScanNumericForecast.fuel 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
            (SourceCurrentConjunctionGuardUniverse.guards heap) profile ≤ p →
          SourceCurrentScanNumericForecast.fuel 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
            (SourceCurrentConjunctionGuardUniverse.guards heap) profile ≤ h →
          SourceCurrentScanNumericForecast.fuel 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
            (SourceCurrentConjunctionGuardUniverse.guards heap) profile ≤ n →
          SourceCurrentAllocatedRecordScanWorker.scan g s p h n 0 values records (before (bits + 2))
            SourceCurrentEmptinessMemo.empty = .done (none, records) (before (bits + 2)) SourceCurrentEmptinessMemo.empty := by
  refine ⟨no_cap, ?_, ?_⟩
  · intro closed
    have impossible := closed (.reference .depth) (by simp [values])
    cases impossible
  · obtain ⟨bits, room⟩ := exists_room
      (SourceCurrentScanNumericForecast.schedule 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
        (SourceCurrentConjunctionGuardUniverse.guards heap) profile).2
    have reserved := reserved_of_room bits 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
      (SourceCurrentConjunctionGuardUniverse.guards heap) profile room
    obtain ⟨outcome, kept, after, saved, next, final, receipt, retained, reads, post, _sublist, _fields,
      _sound, _nodeTable, _edgeTable, _mergeTable, _fourthTable, run⟩ :=
      SourceCurrentRecordScanNumeric.complete formulas solver inventory 0 values records (caller (bits + 2))
        EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver) profile
        (initial_fits _) (available_values _) records_proper records_coherent records_active reserved
    let fuel := SourceCurrentScanNumericForecast.fuel 0 values.length
      (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentConjunctionGuardUniverse.guards heap) profile
    have computed := run fuel fuel fuel fuel fuel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _)
    obtain ⟨g, s, p, h, n, stable⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete
      (expected_retained (bits + 2))
    have literal := stable g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    obtain ⟨same, sameAfter, sameSaved⟩ := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique computed literal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    cases sameAfter
    cases sameSaved
    exact ⟨bits, next, final, receipt, retained, reads, post, rfl, run⟩

/-- Empty original records need no numeric reservation and retain the exact full caller state. -/
theorem constructed_empty_records (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver
          (SourceCurrentConjunctionGuardUniverse.guards heap) profile 0 values []
          (before (bits + 2)) SourceCurrentEmptinessMemo.empty none [] (before (bits + 2))
          SourceCurrentEmptinessMemo.empty next,
        SourceCurrentConjunctionSelectedRecords.Retained receipt.actual [] [] ∧
        SourceCurrentAllocatedScanSourceReads.ScanReads receipt.actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
          (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) (before (bits + 2))
            SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty) final ∧
        SourceCurrentAllocatedRecordScanWorker.scan 0 0 0 0 0 0 values [] (before (bits + 2)) SourceCurrentEmptinessMemo.empty =
          .done (none, []) (before (bits + 2)) SourceCurrentEmptinessMemo.empty := by
  obtain ⟨outcome, kept, after, saved, next, final, receipt, retained, reads, post, _sublist, _fields,
    _sound, _nodeTable, _edgeTable, _mergeTable, _fourthTable, _run⟩ :=
    SourceCurrentRecordScanNumeric.complete formulas solver inventory 0 values [] (caller (bits + 2))
      EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver) profile
      (initial_fits _) (available_values _) (by intro own member; cases member)
      (by intro own member; cases member) (by intro own member; cases member) trivial
  have actual := receipt.actual
  cases actual
  have noRecords := retained.fields.2
  have noKept : kept = [] := List.map_eq_nil_iff.mp noRecords
  subst kept
  exact ⟨next, final, receipt, retained, reads, post, rfl⟩

end MicroCFTA.RecordScanNumericKernels

#check @MicroCFTA.RecordScanNumericKernels.constructed_duplicate_records
#print axioms MicroCFTA.RecordScanNumericKernels.constructed_duplicate_records
#check @MicroCFTA.RecordScanNumericKernels.constructed_empty_records
#print axioms MicroCFTA.RecordScanNumericKernels.constructed_empty_records
