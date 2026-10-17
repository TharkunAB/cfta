import MicroCFTA.SourceCurrentClassesNumeric
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentConjunctionRequiredActual
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

namespace MicroCFTA.ClassesEndToEndReview
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
  .node [.mk ("roots", .top) annotation [
    .node [.mk ("finite", .top) annotation [.node [.mk ("left", .top) annotation []], .node [.mk ("right", .top) annotation []]]],
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[1]?).getD .empty
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
    (fun original member => by simpa [expression, SourceEqualityConstraintOrigins.guards,
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

private theorem no_cap (depth : Nat) : ¬Cap depth recursive := by
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

private def values : List (Value Symbol Guard) := [finite, recursive, .reference .depth]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1.children finite (by cbv; exact .head _)
  · exact (initial width).2.1.children recursive (by cbv; exact .tail _ (.head _))
  · exact InternedNestedProvenance.depth_available _
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
private theorem open_values : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [values])
  cases impossible
private theorem no_forest_cap : ∀ depth, ¬(∀ child ∈ values, Cap depth child) := by
  intro depth bounded
  exact no_cap depth (bounded recursive (by simp [values]))

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

private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] with
  | some own => own
  | none => ⟨.empty, []⟩
private def records := [record]
private theorem record_built : SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] = some record := by cbv
private theorem record_paths : record.paths = [[0, 0], [0, 1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨own, built, coherent, _paths⟩ := SourceEqualityClassOrder.recordOf_complete [[0, 0], [0, 1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0, .branch [(0, .terminal), (1, .terminal)])], by cbv⟩)
  have same : own = record := Option.some.inj (built.symm.trans record_built)
  exact same ▸ coherent
private theorem proper : ∀ own ∈ records, ∀ path ∈ own.paths, path ≠ [] := by
  intro own member path included
  have same : own = record := List.mem_singleton.mp member
  subst own
  rw [record_paths] at included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl <;> decide
private theorem coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  exact (List.mem_singleton.mp member) ▸ record_coherent
private theorem active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = record := List.mem_singleton.mp member
  subst own
  rw [record_paths]
  exact ⟨[0, 0], by simp, [0, 1], by simp, by decide⟩
private theorem primary (state : State Symbol Guard) :
    EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values record.paths state false state := by
  rw [record_paths]
  exact .next (.child (.present rfl (by cbv; exact .finite (by decide))))
    (.next (.child (.present rfl (by cbv; exact .finite (by decide)))) .nil)
private theorem expected (width : Nat) : SourceCurrentConjunctionClassScan.Scan 0 SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
    (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty
    none (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty :=
  .selected (primary heap) .nil
private theorem expected_retained (width : Nat) :
    SourceCurrentConjunctionSelectedRecords.Retained (expected width) records records :=
  .selected (primary := primary heap) (rest := .nil) rfl .nil

private theorem selected_shape {width : Nat} {outcome kept after saved}
    {actual : SourceCurrentConjunctionClassScan.Scan 0 SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty
      outcome (kept.map SourceEqualityClassOrder.Record.paths) after saved}
    (retained : SourceCurrentConjunctionSelectedRecords.Retained actual records kept) :
    outcome = none ∧ kept = records := by
  obtain ⟨g, s, p, h, n, first⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
  obtain ⟨G, S, P, H, N, last⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete (expected_retained width)
  have same := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique
    (first g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (last G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact Prod.mk.inj same.1

private theorem raw_scan_shape {width : Nat} {outcome selected after saved}
    (actual : SourceCurrentConjunctionClassScan.Scan 0 SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) (before width) SourceCurrentEmptinessMemo.empty
      outcome selected after saved) : outcome = none ∧ selected = records.map SourceEqualityClassOrder.Record.paths := by
  obtain ⟨g,s,p,h,n,first⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete actual
  obtain ⟨G,S,P,H,N,last⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete (expected width)
  have same := SourceCurrentAllocatedScanWorkerStability.scan_done_unique
    (first g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (last G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact Prod.mk.inj same.1

private theorem reduction_outcome {width : Nat} {outcome results after savedFourth saved}
    (actual : SourceCurrentConjunctionScanClassPass.Reduction 0 records values (before width)
      SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty outcome results after savedFourth saved) : outcome = none := by
  cases actual with
  | stopped scan => exact (raw_scan_shape scan).1
  | completed => rfl

private theorem reduction_pass {width : Nat} {results after savedFourth saved}
    (actual : SourceCurrentConjunctionScanClassPass.Reduction 0 records values (before width)
      SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty none results after savedFourth saved) :
    ∃ kept prepared middle,
      kept.Sublist records ∧ kept ≠ [] ∧
      SourceCurrentAllocatedClassPass.Pass kept prepared middle SourceCurrentMemoMergeGraph.empty results after saved := by
  cases actual with
  | completed scan retained required pass =>
      refine ⟨_, _, _, retained.fields.1, ?_, pass⟩
      intro absent
      have projected := retained.fields.2
      rw [absent] at projected
      have impossible := projected.trans (raw_scan_shape scan).2
      cases impossible

private noncomputable def fullFuel := SourceCurrentClassesForecast.fuel 0 values.length records
  (SourceCurrentConjunctionGuardUniverse.guards heap) profile
private noncomputable def fullProfile := SourceCurrentClassesForecast.finalProfile 0 values.length records
  (SourceCurrentConjunctionGuardUniverse.guards heap) profile

/-- Own initial source facts construct the full original class worker on an uncapped open forest and a reached nonempty pass. -/
theorem constructed_nonempty_classes
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬(∀ child ∈ values, Cap depth child)) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ bits results after savedFourth saved next final,
      ∃ _receipt : SourceCurrentClassesNumeric.Receipt formulas solver next profile 0 records values
          (caller (bits + 2)) EndpointMemoGateTrace.empty none results after savedFourth saved final,
        (∃ kept prepared middle, kept.Sublist records ∧ kept ≠ [] ∧
          SourceCurrentAllocatedClassPass.Pass kept prepared middle SourceCurrentMemoMergeGraph.empty results after saved) ∧
        Frame formulas solver next after ∧ Fits fullProfile after ∧
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
          (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after savedFourth saved) final ∧
        ∀ g s r e p h m c n,
          fullFuel ≤ g → fullFuel ≤ s → fullFuel ≤ r → fullFuel ≤ e → fullFuel ≤ p →
          fullFuel ≤ h → fullFuel ≤ m → fullFuel ≤ c → fullFuel ≤ n →
          SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n 0 records values (before (bits + 2))
            SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty = .done results after savedFourth saved := by
  obtain ⟨bits, room⟩ := exists_room fullProfile
  have scanRoom := room.mono
    ((SourceCurrentScanRequiredForecast.scan_le 0 values.length records (SourceCurrentConjunctionGuardUniverse.guards heap) profile).trans
      (SourceCurrentClassesForecast.preparation_le 0 values.length records (SourceCurrentConjunctionGuardUniverse.guards heap) profile))
  have reserved : SourceCurrentClassesForecast.Reserved bits 0 values.length records
      (SourceCurrentConjunctionGuardUniverse.guards heap) profile :=
    ⟨reserved_of_room bits 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
      (SourceCurrentConjunctionGuardUniverse.guards heap) profile scanRoom, room⟩
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, receipt⟩ :=
    SourceCurrentClassesNumeric.complete formulas solver inventory 0 values records (caller (bits + 2)) EndpointMemoGateTrace.empty
      (context _ formulas solver) (initial_frame bits formulas solver) profile (initial_fits _) (available_values (bits + 2))
      proper coherent active reserved
  have noneOutcome := reduction_outcome receipt.actual
  cases noneOutcome
  exact ⟨no_forest_cap, open_values, bits, results, after, savedFourth, saved, next, final, receipt,
    reduction_pass receipt.actual, receipt.frame, receipt.fits, receipt.post, receipt.run⟩

private theorem empty_classes_done (width : Nat) :
    SourceCurrentAllocatedLocalWorker.classes 0 0 0 0 0 0 0 0 0 0 [] values (before width)
      SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty =
      .done values (before width) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty := by
  have emptyPaths : SourceEqualitySelectedRequired.paths [] = [] := by
    simp [SourceEqualitySelectedRequired.paths, EqualityNormalize.canonicalClass]
  have unchanged : EqualityLeafProjectionRuntimeEmpty.propagate values = values := by cbv
  simp only [SourceCurrentAllocatedLocalWorker.classes, SourceCurrentAllocatedLocalWorker.scan,
    SourceCurrentAllocatedRecordScanWorker.scan, SourceCurrentAllocatedLocalWorker.Outcome.bind,
    SourceCurrentAllocatedLocalWorker.required, List.map_nil, emptyPaths, SourceEqualityRequiredExecution.requireAll_identity,
    SourceCurrentAllocatedLocalWorker.pass, SourceCurrentAllocatedClassWorker.pass, SourceCurrentAllocatedClassWorker.fold,
    SourceCurrentAllocatedClassWorker.Outcome.bind, unchanged]
  rfl

/-- Empty original records construct the same full caller without any Room premise and execute at zero fuels. -/
theorem constructed_empty_classes (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ outcome next final,
      ∃ _receipt : SourceCurrentClassesNumeric.Receipt formulas solver next profile 0 [] values
          (caller (bits + 2)) EndpointMemoGateTrace.empty outcome values (before (bits + 2))
          SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty final,
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2)) (caller (bits + 2)) final ∧
        SourceCurrentAllocatedLocalWorker.classes 0 0 0 0 0 0 0 0 0 0 [] values (before (bits + 2))
          SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty =
          .done values (before (bits + 2)) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty := by
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, receipt⟩ :=
    SourceCurrentClassesNumeric.complete formulas solver inventory 0 values [] (caller (bits + 2)) EndpointMemoGateTrace.empty
      (context _ formulas solver) (initial_frame bits formulas solver) profile (initial_fits _) (available_values (bits + 2))
      (by intro own member; cases member) (by intro own member; cases member) (by intro own member; cases member) ⟨trivial, trivial⟩
  let fuel := SourceCurrentClassesForecast.fuel 0 values.length [] (SourceCurrentConjunctionGuardUniverse.guards heap) profile
  have completed := receipt.run fuel fuel fuel fuel fuel fuel fuel fuel fuel
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have same := SourceCurrentAllocatedLocalWorkerStability.classes_done_unique completed (empty_classes_done (bits + 2))
  obtain ⟨sameValues, sameAfter, sameFourth, sameMerge⟩ := same
  cases sameValues
  cases sameAfter
  cases sameFourth
  cases sameMerge
  exact ⟨outcome, next, final, receipt, receipt.post, empty_classes_done _⟩

end MicroCFTA.ClassesEndToEndReview

#check @MicroCFTA.ClassesEndToEndReview.constructed_nonempty_classes
#print axioms MicroCFTA.ClassesEndToEndReview.constructed_nonempty_classes
#check @MicroCFTA.ClassesEndToEndReview.constructed_empty_classes
#print axioms MicroCFTA.ClassesEndToEndReview.constructed_empty_classes
