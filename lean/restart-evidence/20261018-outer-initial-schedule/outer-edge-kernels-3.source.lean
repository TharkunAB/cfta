import MicroCFTA.SourceCurrentOuterEdgeGuardAlphabet
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

namespace MicroCFTA.OuterEdgeKernels
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
private def nextProfile := SourceCurrentParentUniformEnvelope.profile 0 alphabet profile
private def nextAlphabet := SourceCurrentParentUniformGuardAlphabet.forecast 0 alphabet profile
private def roomProfile := SourceCurrentInitialSelectionForecast.cover
  [SourceCurrentParentUniformEnvelope.classesProfile 0 alphabet profile,
   SourceCurrentParentUniformEnvelope.classesProfile 0 nextAlphabet nextProfile] profile
private def widthBits := SourceCurrentParentInitialRoom.roomBits roomProfile
private def running : SourceCurrentAllocatedPartialState.State (widthBits+2) :=
  (SourceCurrentAllocatedPartialState.beginEdge request (caller (widthBits+2))).2.2
private theorem cold_start : SourceCurrentAllocatedPartialState.beginEdge request (caller (widthBits+2)) =
    (0, .evaluate request, running) := rfl
private theorem running_checked : running.checked = (caller (widthBits+2)).checked :=
  (SourceCurrentAllocatedPartialState.beginEdge_components request (caller (widthBits+2))).1
private theorem first_uniform : SourceCurrentParentAlphabetReservation.UniformReserved widthBits 0 alphabet profile :=
  SourceCurrentParentInitialRoom.uniform_of_room _ _ _ _
    ((SourceCurrentParentInitialRoom.room_computed roomProfile).mono
      (SourceCurrentInitialSelectionForecast.cover_member profile (by simp)))
private theorem second_uniform : SourceCurrentParentAlphabetReservation.UniformReserved widthBits 0 nextAlphabet nextProfile :=
  SourceCurrentParentInitialRoom.uniform_of_room _ _ _ _
    ((SourceCurrentParentInitialRoom.room_computed roomProfile).mono
      (SourceCurrentInitialSelectionForecast.cover_member profile (by simp)))

private theorem finish_table (handle : Nat) (result : EdgeValue Symbol Guard)
    (state : FlatMemoThunk.State SourceCurrentAllocatedPartialState.EdgeKey
      SourceCurrentAllocatedPartialState.EdgeRequest (EdgeValue Symbol Guard)) :
    (FlatMemoThunk.finish handle result state).table = state.table := by
  cases found : state.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk owner phase => cases phase <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

private theorem published {result : EdgeValue Symbol Guard}
    {after : SourceCurrentAllocatedPartialState.State (widthBits+2)}
    (actual : SourceCurrentAllocatedPartialGraph.EdgeCall 0 request (caller (widthBits+2)) result after) :
    after.edgeResults.table request.key = some 0 := by
  cases actual with
  | hit started => rw [cold_start] at started; cases started
  | evaluate started body =>
      rw [cold_start] at started
      cases started
      have protection := SourceCurrentAllocatedPartialFrames.edge_body body
        (SourceCurrentAllocatedPartialFrames.Protocol.of_valid
          (SourceCurrentAllocatedPartialState.beginEdge_valid request (caller (widthBits+2))
            (SourceCurrentAllocatedPartialState.initial_valid _ _ _) (empty_ready (widthBits+2)).1))
      have first : running.edgeResults.table request.key = some 0 := by
        change Cache.put (fun _ => none) request.key 0 request.key = some 0
        simp only [Cache.put,ite_true]
      change (FlatMemoThunk.finish _ _ _).table _ = _
      rw [finish_table]
      exact protection.edge_keys _ _ first

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ built = .done value heap ∧
    ∃ result after next final warmNext warmFinal,
      SourceCurrentEdgeCallNumeric.Receipt formulas solver next profile 0 request (caller (widthBits+2))
        EndpointMemoGateTrace.empty result after final ∧
      Fits nextProfile after.checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ nextAlphabet) after.checked.native.machine.heap ∧
      after.edgeResults.cells 0 = some ⟨request,.returned result⟩ ∧
      after.edgeResults.table request.key = some 0 ∧
      SourceCurrentEdgeCallNumeric.Receipt formulas solver warmNext nextProfile 0 request after final result after warmFinal ∧
      Fits (SourceCurrentParentUniformEnvelope.profile 0 nextAlphabet nextProfile) after.checked ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => guard ∈ SourceCurrentParentUniformGuardAlphabet.forecast 0 nextAlphabet nextProfile)
        after.checked.native.machine.heap ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 request after = .done result after := by
  have known := SourceCurrentConjunctionGuardUniverse.initial heap (initial (widthBits+2)).1.good.native.machine.1
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory 0 alphabet request
    (caller (widthBits+2)) EndpointMemoGateTrace.empty (context (widthBits+2) formulas solver) profile
    (initial_fits (widthBits+2)) known (empty_ready (widthBits+2)) source_resident first_uniform
  have callReserved : SourceCurrentEdgeCallNumeric.Reserved widthBits 0 request (caller (widthBits+2)) profile := by
    simpa only [SourceCurrentEdgeCallNumeric.Reserved,cold_start,running_checked] using reserved
  obtain ⟨result,after,next,final,computed,cell⟩ := SourceCurrentEdgeCallNumeric.evaluated formulas solver inventory 0 request
    (caller (widthBits+2)) EndpointMemoGateTrace.empty (context (widthBits+2) formulas solver)
    (initial_frame widthBits formulas solver) profile (initial_fits (widthBits+2))
    (empty_ready (widthBits+2)) source_resident callReserved cold_start
  let bound := SourceCurrentEdgeCallNumeric.fuel 0 request (caller (widthBits+2)) profile
  have done := computed.run 0 bound bound bound bound bound bound bound bound bound
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨current,currentMemos,cold,numeric,carrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver inventory 0
    alphabet request (caller (widthBits+2)) EndpointMemoGateTrace.empty (context (widthBits+2) formulas solver)
    (initial_frame widthBits formulas solver) profile (initial_fits (widthBits+2)) known
    (empty_ready (widthBits+2)) source_resident first_uniform done
  have table := published cold.actual
  have hit := SourceCurrentAllocatedPartialState.beginEdge_ready request request after 0 result table cell
  have warmDone := SourceCurrentAllocatedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0 0 request after after 0 result hit
  have inherited := (empty_ready (widthBits+2)).grows cold.semantic.effects.grows.constraint_growth
  have resident := InternedEdgeResidency.edge_grows _ _ cold.semantic.effects.keeps.growth
    request.value source_resident
  obtain ⟨warmNext,warmFinal,warm,warmFits,warmCarrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver current 0
    nextAlphabet request after currentMemos cold.post.context cold.frame nextProfile numeric carrier inherited resident second_uniform warmDone
  exact ⟨no_cap,constructed,result,after,current,currentMemos,warmNext,warmFinal,cold,numeric,carrier,
    cell,table,warm,warmFits,warmCarrier,warmDone⟩

/-- An initial constrained recursive source produces a cold owner and an exact zero-fuel warm hit. -/
theorem cold_warm (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ built = .done value heap ∧
    ∃ result after next final warmNext warmFinal,
      SourceCurrentEdgeCallNumeric.Receipt formulas solver next profile 0 request (caller (widthBits+2))
        EndpointMemoGateTrace.empty result after final ∧
      Fits nextProfile after.checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ nextAlphabet) after.checked.native.machine.heap ∧
      after.edgeResults.cells 0 = some ⟨request,.returned result⟩ ∧
      after.edgeResults.table request.key = some 0 ∧
      SourceCurrentEdgeCallNumeric.Receipt formulas solver warmNext nextProfile 0 request after final result after warmFinal ∧
      Fits (SourceCurrentParentUniformEnvelope.profile 0 nextAlphabet nextProfile) after.checked ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => guard ∈ SourceCurrentParentUniformGuardAlphabet.forecast 0 nextAlphabet nextProfile)
        after.checked.native.machine.heap ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 request after = .done result after :=
  witness formulas solver

end MicroCFTA.OuterEdgeKernels
