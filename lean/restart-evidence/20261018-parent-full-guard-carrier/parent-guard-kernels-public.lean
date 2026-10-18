import MicroCFTA.SourceCurrentParentGuardAlphabet
import MicroCFTA.SourceCurrentParentInitialRoom
import MicroCFTA.SourceCurrentActualParentSemanticReads
import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentLocalNumeric
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 1000000

noncomputable section

namespace MicroCFTA.ParentGuardKernels
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

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("outer", .top) annotation [
    .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]]),
    .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[0]?).getD .empty
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
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
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

private def values : List (Value Symbol Guard) := [finite, recursive]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact (initial width).2.1.children finite (by cbv; exact .head _)
  · exact (initial width).2.1.children recursive (by cbv; exact .head _)
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
private theorem no_forest_cap : ∀ depth, ¬(∀ child ∈ values, Cap depth child) := by
  intro depth bounded
  exact no_cap depth (bounded recursive (by simp [values]))

private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0], [1]] with
  | some own => own
  | none => ⟨.empty, []⟩
private def records := [record]
private theorem record_built : SourceEqualityClassOrder.recordOf [[0], [1]] = some record := by cbv
private theorem record_paths : record.paths = [[0], [1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨own, built, coherent, _paths⟩ := SourceEqualityClassOrder.recordOf_complete [[0], [1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.terminal),(1,.terminal)], by cbv⟩)
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
  exact ⟨[0], by simp, [1], by simp, by decide⟩
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
    let term : Language.Term Symbol := .node ("outer", .top) [.node ("leaf", .top) [], .node ("leaf", .top) []]
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

private theorem live_raw : SourceEqualityMkEdgeAllocation.contradictory annotation = false := by cbv
private theorem live_inputs (width : Nat) : SourceCurrentParentNumeric.LiveInputs annotation loaded emptyField values (caller width) := by
  intro _
  exact ⟨cached,load_live,empty_ready width,available_values width⟩
private def sourceRow : EdgeValue Symbol Guard := ((InternedEdgeResidency.nodeEdges value)[0]?).getD
  ((run (makeEdge ("fallback",.top) annotation []) empty).1)
private def request : SourceCurrentAllocatedPartialState.EdgeRequest := ⟨emptyField,sourceRow⟩
private theorem source_row : sourceRow ∈ InternedEdgeResidency.nodeEdges value ∧
    sourceRow.entry.key.symbol = ("outer",.top) ∧ sourceRow.entry.key.constraint = annotation ∧ sourceRow.children = values := by
  refine ⟨?_,by cbv,by cbv,by cbv⟩
  cbv
  exact List.mem_cons_self
private theorem source_resident : InternedEdgeResidency.EdgeResident heap sourceRow :=
  InternedEdgeResidency.resident_edges heap (initial 0).1.good.native.machine.1.linked value
    (initial 0).2.1.resident sourceRow source_row.1
private def alphabet : List Guard := SourceCurrentConjunctionGuardUniverse.guards heap
private def widthBits := SourceCurrentParentInitialRoom.roomBits
  (SourceCurrentParentUniformEnvelope.classesProfile 0 alphabet profile)
private def lowerFuel := SourceCurrentParentForecast.residentFuel 0 request (before (widthBits+2)) profile

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ built = .done value heap ∧
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard emptyField operations).1 = .ok (.classes records) ∧
    ∃ loaded result after savedFourth saved next final,
      SourceCurrentParentNumeric.Receipt formulas solver next profile 0 request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children
        (caller (widthBits+2)) EndpointMemoGateTrace.empty result after savedFourth saved final ∧
      Fits (SourceCurrentParentForecast.residentProfile 0 request (before (widthBits+2)) profile) after ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ SourceCurrentParentGuardAlphabet.residentForecast
        alphabet 0 request (before (widthBits+2)) profile) after.native.machine.heap ∧
      SourceCurrentAllocatedParentWorker.edge
        (lowerFuel+1) (lowerFuel+2) (lowerFuel+3) (lowerFuel+4) (lowerFuel+5)
        (lowerFuel+6) (lowerFuel+7) (lowerFuel+8) (lowerFuel+9)
        0 request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
        (before (widthBits+2)) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty =
          .done result after savedFourth saved := by
  have known := SourceCurrentConjunctionGuardUniverse.initial heap (initial (widthBits+2)).1.good.native.machine.1
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory 0 alphabet request
    (caller (widthBits+2)) EndpointMemoGateTrace.empty (context (widthBits+2) formulas solver) profile
    (initial_fits (widthBits+2)) known (empty_ready (widthBits+2)) source_resident
    (SourceCurrentParentInitialRoom.uniform_computed 0 alphabet profile)
  obtain ⟨loaded,result,after,savedFourth,saved,next,final,receipt,numeric,carrier,done⟩ :=
    SourceCurrentParentGuardAlphabet.resident_complete alphabet formulas solver inventory 0 request
      (caller (widthBits+2)) EndpointMemoGateTrace.empty (context (widthBits+2) formulas solver)
      (initial_frame widthBits formulas solver) profile (initial_fits (widthBits+2))
      (fun _ => source_resident) (fun _ => empty_ready (widthBits+2)) reserved known
  exact ⟨no_cap,constructed,live_branch,loaded,result,after,savedFourth,saved,next,final,receipt,numeric,carrier,
    done _ _ _ _ _ _ _ _ _ (Nat.le_add_right _ 1) (Nat.le_add_right _ 2) (Nat.le_add_right _ 3)
      (Nat.le_add_right _ 4) (Nat.le_add_right _ 5) (Nat.le_add_right _ 6) (Nat.le_add_right _ 7)
      (Nat.le_add_right _ 8) (Nat.le_add_right _ 9)⟩

/-- Initial constructed recursive children produce the complete Parent carrier at independently larger nine fuels. -/
theorem recursive_parent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ built = .done value heap ∧
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard emptyField operations).1 = .ok (.classes records) ∧
    ∃ loaded result after savedFourth saved next final,
      SourceCurrentParentNumeric.Receipt formulas solver next profile 0 request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children
        (caller (widthBits+2)) EndpointMemoGateTrace.empty result after savedFourth saved final ∧
      Fits (SourceCurrentParentForecast.residentProfile 0 request (before (widthBits+2)) profile) after ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ SourceCurrentParentGuardAlphabet.residentForecast
        alphabet 0 request (before (widthBits+2)) profile) after.native.machine.heap ∧
      SourceCurrentAllocatedParentWorker.edge
        (lowerFuel+1) (lowerFuel+2) (lowerFuel+3) (lowerFuel+4) (lowerFuel+5)
        (lowerFuel+6) (lowerFuel+7) (lowerFuel+8) (lowerFuel+9)
        0 request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
        (before (widthBits+2)) SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty =
          .done result after savedFourth saved :=
  witness formulas solver

end MicroCFTA.ParentGuardKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
#check @MicroCFTA.ParentGuardKernels.recursive_parent
#print MicroCFTA.ParentGuardKernels.recursive_parent
#print axioms MicroCFTA.ParentGuardKernels.recursive_parent
