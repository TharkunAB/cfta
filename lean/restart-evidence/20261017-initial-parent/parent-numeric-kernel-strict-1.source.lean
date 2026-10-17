import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentAllocatedClassEditPlan
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
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 1000000

namespace MicroCFTA.ParentNumericKernels
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

private def annotation : Guard := ⟨some [[[0, 0], [0, 1]]], .top⟩
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
private def emptyOriginal : Guard := ⟨some [], .top⟩
private def allocatedEmpty := SourceEqualityConstraintAllocation.construct emptyOriginal.equalities allocated.2
private def emptyField : SourceEqualityConstraintAllocation.Value := match allocatedEmpty.1 with
  | .ok own => own
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocatedEmpty.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0, 0], [0, 1]]] = .normalized [[[0, 0], [0, 1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocatedEmpty.2 [annotation, emptyOriginal] := by
  have first : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached allocation
  have last : allocatedEmpty = (.ok emptyField, allocatedEmpty.2) := by cbv
  exact SourceEqualityOriginalAllocationHistory.History.construct first SourceEqualityGuardReadback.empty_cached last
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by
      have same : original = annotation := by simpa [expression, SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards] using member
      subst original
      exact List.mem_cons_self) value heap constructed
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

private def loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨field, .top⟩
private def emptyLoaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨emptyField, .top⟩
private theorem load_live : SourceEqualityConstraintFieldLookup.load annotation operations.constraints = .ok (some loaded) := by cbv
private theorem load_empty : SourceEqualityConstraintFieldLookup.load emptyOriginal operations.constraints = .ok (some emptyLoaded) := by cbv
private theorem empty_ready (width : Nat) : SourceEqualityConstraintAllocation.Ready operations.constraints emptyField :=
  (SourceEqualityConstraintFieldLookup.load_ready emptyOriginal operations.constraints
    (initial width).1.good.operations.constraints SourceEqualityGuardReadback.empty_cached emptyLoaded load_empty).1
private theorem live_branch : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard emptyField operations).1 =
    .ok (.classes records) := by
  have valid := (initial 0).1.good.operations
  have storedReady := (SourceEqualityConstraintFieldLookup.load_ready annotation operations.constraints
    valid.constraints cached loaded load_live).1
  have built := SourceEqualityConstraintFieldLookup.load_constructor_receipt annotation operations.constraints cached loaded load_live
  obtain ⟨own, branch, ownRead, actual, exactBranch, _valid, _growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard emptyField operations
      valid storedReady (empty_ready 0) annotation.equalities cached built
  have entry := (SourceEqualityPhysicalClassEntry.entry_of_own annotation emptyField.payload own.payload ownRead).trans exactBranch
  have expected : SourceEqualityPhysicalClassEntry.entry annotation emptyField.payload = .ok (.classes records) := by
    have ownBuilt : SourceEqualityPhysicalPayload.own annotation = .ok (some records) := by cbv
    have inherited : emptyField.payload = some [] := by cbv
    rw [SourceEqualityPhysicalClassEntry.entry_of_own annotation emptyField.payload (some records) ownBuilt, inherited]
    let term : Language.Term Symbol := .node ("outer", .top) [.node ("inner", .top) [.node ("leaf", .top) [], .node ("leaf", .top) []]]
    have accepted : EqualityNormalize.RunSat term (SourceEqualityPrecheck.combine (some records) (some [])) :=
      (SourceEqualityPrecheck.combine_exact (some records) (some []) term).mpr (by
        simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies, EqualityNormalize.ClassSat,
          records, record_paths, Language.PathsEqual, term, Language.Term.atPath])
    have notRejected : SourceEqualityPrecheck.rejects (SourceEqualityPrecheck.combine (some records) (some [])) = false := by
      cases result : SourceEqualityPrecheck.combine (some records) (some []) with
      | timeout => rw [result] at accepted; cases accepted
      | contradiction => rw [result] at accepted; cases accepted
      | normalized classes => rfl
    have nonempty : SourceEqualityPrecheck.isEmpty (some records) = false := rfl
    have ordered : SourceEqualityClassOrder.ordered records = records := by cbv
    simp only [SourceEqualityPrecheck.precheck, nonempty, Bool.false_and, Bool.false_eq_true,
      ite_false, notRejected, SourceEqualityPrecheck.unsafeOrdered, Except.map, ordered]
  have same : branch = .classes records := Except.ok.inj (entry.symm.trans expected)
  exact actual.trans (congrArg Except.ok same)
private theorem unchanged_branch : (SourceEqualityPartialPrecheckAllocation.run emptyLoaded.stored emptyLoaded.guard emptyField operations).1 =
    .ok .unchanged := by cbv
private theorem erased_branch : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard .contradiction operations).1 =
    .ok .emptyChildren := by cbv

private theorem classes_reserved_of_room (bits : Nat)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      (SourceCurrentClassesForecast.finalProfile 0 values.length records
        (SourceCurrentConjunctionGuardUniverse.guards heap) profile)) :
    SourceCurrentClassesForecast.Reserved bits 0 values.length records
      (SourceCurrentConjunctionGuardUniverse.guards heap) profile := by
  have preparation := room.mono (SourceCurrentClassesForecast.preparation_le 0 values.length records
    (SourceCurrentConjunctionGuardUniverse.guards heap) profile)
  have scanRoom := preparation.mono (SourceCurrentScanRequiredForecast.scan_le 0 values.length records
    (SourceCurrentConjunctionGuardUniverse.guards heap) profile)
  have scanReserved := reserved_of_room bits 0 values.length (records.map SourceEqualityClassOrder.Record.paths)
    (SourceCurrentConjunctionGuardUniverse.guards heap) profile scanRoom
  exact ⟨scanReserved, room⟩

/-- An own initial profile completes a live parent over an uncapped and open child forest. -/
theorem constructed_live
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬(∀ child ∈ values, Cap depth child)) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ bits result after fourth memo next final,
      ∃ _receipt : SourceCurrentParentNumeric.Receipt formulas solver next profile 0 ("parent", .top) annotation loaded emptyField values
          (caller (bits + 2)) EndpointMemoGateTrace.empty result after fourth memo final,
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard emptyField operations).1 = .ok (.classes records) := by
  obtain ⟨bits, room⟩ := exists_room (SourceCurrentClassesForecast.finalProfile 0 values.length records
    (SourceCurrentConjunctionGuardUniverse.guards heap) profile)
  have localRoom : SourceCurrentLocalForecast.Reserved bits 0 values.length loaded emptyField (before (bits + 2)) profile := by
    unfold SourceCurrentLocalForecast.Reserved
    change (match (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard emptyField operations).1 with
      | .ok (.classes own) => SourceCurrentClassesForecast.Reserved bits 0 values.length own
          (SourceCurrentConjunctionGuardUniverse.guards heap) profile
      | _ => True)
    rw [live_branch]
    exact classes_reserved_of_room bits room
  have rawLive : SourceEqualityMkEdgeAllocation.contradictory annotation = false := by cbv
  have reserved : SourceCurrentParentForecast.Reserved bits 0 values.length annotation loaded emptyField (before (bits + 2)) profile := by
    simpa only [SourceCurrentParentForecast.Reserved, rawLive, Bool.false_eq_true, ite_false] using localRoom
  have live : SourceCurrentParentNumeric.LiveInputs annotation loaded emptyField values (caller (bits + 2)) :=
    fun _ => ⟨cached, load_live, empty_ready 0, available_values 0⟩
  obtain ⟨result, after, fourth, memo, next, final, receipt⟩ := SourceCurrentParentNumeric.complete formulas solver inventory 0
    ("parent", .top) annotation loaded emptyField values (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver)
    (initial_frame bits formulas solver) profile (initial_fits _) live reserved
  exact ⟨no_forest_cap, open_values, bits, result, after, fourth, memo, next, final, receipt, live_branch⟩

/-- Raw rejection skips a missing field and arbitrary inherited or unavailable child inputs. -/
theorem constructed_rejected (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (children : List (Value Symbol Guard)) :
    let original : Guard := ⟨some [[[77], [78]]], .bottom⟩
    let loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨.live 123 [], .bottom⟩
    let actual := SourceCurrentAllocatedMkEdge.reject ("rejected", .top) (before (bits + 2))
    SourceEqualityConstraintFieldLookup.load original operations.constraints = .ok none ∧
      SourceCurrentParentNumeric.Receipt formulas solver inventory profile 0 ("rejected", .top) original loaded inherited children
        (caller (bits + 2)) EndpointMemoGateTrace.empty actual.1 actual.2
        SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty EndpointMemoGateTrace.empty ∧
      SourceCurrentAllocatedParentWorker.edge 0 0 0 0 0 0 0 0 0 0 ("rejected", .top) original inherited children
        (before (bits + 2)) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty =
        .done actual.1 actual.2 SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty := by
  dsimp only
  have test : SourceEqualityMkEdgeAllocation.contradictory (⟨some [[[77], [78]]], .bottom⟩ : Guard) = true := rfl
  refine ⟨?_, SourceCurrentParentNumeric.rejected formulas solver inventory 0 ("rejected", .top) _ _ inherited children
    (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver)
    profile (initial_fits _) test, ?_⟩
  · cbv
  · exact SourceCurrentAllocatedParentWorker.edge_rejected 0 0 0 0 0 0 0 0 0 0 ("rejected", .top) _ inherited children
      (before (bits + 2)) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty test

end MicroCFTA.ParentNumericKernels
