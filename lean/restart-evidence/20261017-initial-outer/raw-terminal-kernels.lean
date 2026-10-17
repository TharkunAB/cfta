import MicroCFTA.SourceCurrentRawRebuildNumeric
import MicroCFTA.SourceCurrentNodeTerminalNumeric
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

namespace MicroCFTA.RawTerminalIntegration
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

private def emptyLoaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨emptyField, .top⟩
private theorem load_empty : SourceEqualityConstraintFieldLookup.load emptyOriginal operations.constraints = .ok (some emptyLoaded) := by cbv
private theorem empty_ready (width : Nat) : SourceEqualityConstraintAllocation.Ready operations.constraints emptyField :=
  (SourceEqualityConstraintFieldLookup.load_ready emptyOriginal operations.constraints
    (initial width).1.good.operations.constraints SourceEqualityGuardReadback.empty_cached emptyLoaded load_empty).1

private def sourceRows := InternedEdgeResidency.nodeEdges value
private def originalEntry : Interned InternedBinderProtocol.NodeKey := match value with
  | .node entry _ _ _ => entry
  | _ => ⟨0, .empty⟩
private theorem node_shape : value = .node originalEntry sourceRows value.depth value.free := by cbv
private def originalEdge : EdgeValue Symbol Guard := match value with
  | .node _ (edge :: _) _ _ => edge
  | _ => .mk ⟨0, ⟨("missing", .top), [], emptyOriginal⟩⟩ []
private def replacements : List (Value Symbol Guard) := [recursive, .reference .depth]
private def rawBuilt (width : Nat) := SourceCurrentAllocatedRawRebuild.edge originalEdge replacements (before width)
private def modified (width : Nat) := SourceCurrentAllocatedRawRebuild.modify value sourceRows [(rawBuilt width).1] (rawBuilt width).2
private def finalProfile := SourceCurrentRawRebuildNumeric.constructorProfile 1
  (SourceCurrentRawRebuildNumeric.constructorProfile replacements.length profile)
private theorem original_resident : InternedEdgeResidency.EdgeResident heap originalEdge := by cbv
private theorem replacement_available : InternedNestedProvenance.Values heap replacements := by
  intro child member
  simp only [replacements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact available_values 0 recursive (by simp [values])
  · exact InternedNestedProvenance.depth_available _
private theorem original_arity : replacements.length = originalEdge.children.length := by cbv

/-- Own open non-Cap replacements pass through raw edge construction and a changed ordinary rebuild. -/
theorem constructed_changed_raw (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory originalEdge replacements (before (bits + 2))
      (rawBuilt (bits + 2)).1 (rawBuilt (bits + 2)).2 ∧
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory value sourceRows [(rawBuilt (bits + 2)).1]
      (rawBuilt (bits + 2)).2 (modified (bits + 2)).1 (modified (bits + 2)).2 ∧
    Frame formulas solver inventory (modified (bits + 2)).2 ∧ Fits finalProfile (modified (bits + 2)).2 ∧
    (modified (bits + 2)).2.operations = operations ∧
    [(rawBuilt (bits + 2)).1.entry.identity] ≠ sourceRows.map (fun edge => edge.entry.identity) ∧
    SourceCurrentAllocatedRawRebuild.edge originalEdge replacements (rawBuilt (bits + 2)).2 = rawBuilt (bits + 2) := by
  obtain ⟨edgeReceipt, edgeFrame, edgeFits, _nodes, _edges⟩ := SourceCurrentRawRebuildNumeric.edge
    formulas solver inventory originalEdge replacements (before (bits + 2)) (initial_frame bits formulas solver) profile
    (initial_fits _) original_resident replacement_available original_arity
  have inputAvailable := edgeReceipt.effects.keeps.available value (initial (bits + 2)).2.1
  have rowsResident : InternedNestedProvenance.Edges (rawBuilt (bits + 2)).2.native.machine.heap [(rawBuilt (bits + 2)).1] := by
    intro row member
    cases List.mem_singleton.mp member
    exact edgeReceipt.resident
  have shape : ∃ entry rows depth free, value = .node entry rows depth free :=
    ⟨originalEntry, sourceRows, value.depth, value.free, node_shape⟩
  obtain ⟨entry, rows, depth, free, shape⟩ := shape
  have originalRows : sourceRows = rows := by rw [sourceRows, shape]; rfl
  have nodeResult := SourceCurrentRawRebuildNumeric.modify formulas solver inventory entry rows [(rawBuilt (bits + 2)).1]
    depth free (rawBuilt (bits + 2)).2 edgeFrame (SourceCurrentRawRebuildNumeric.constructorProfile replacements.length profile)
    edgeFits (shape ▸ inputAvailable) rowsResident
  dsimp only at nodeResult
  rw [← shape, ← originalRows] at nodeResult
  obtain ⟨nodeReceipt, nodeFrame, nodeFits, _nodeCounter, _edgeCounter⟩ := nodeResult
  refine ⟨no_cap, edgeReceipt, nodeReceipt, nodeFrame, nodeFits, nodeReceipt.operations.trans edgeReceipt.operations, ?_, ?_⟩
  · cbv; decide
  · cbv

/-- The actual identity comparison retains the exact initial full state at the same forecast. -/
theorem constructed_unchanged_raw (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedRawRebuild.modify value sourceRows sourceRows (before (bits + 2)) = (value, before (bits + 2)) ∧
    Frame formulas solver inventory (before (bits + 2)) ∧
    Fits (SourceCurrentRawRebuildNumeric.constructorProfile sourceRows.length profile) (before (bits + 2)) := by
  have shape : ∃ entry rows depth free, value = .node entry rows depth free :=
    ⟨originalEntry, sourceRows, value.depth, value.free, node_shape⟩
  obtain ⟨entry, rows, depth, free, shape⟩ := shape
  have originalRows : sourceRows = rows := by rw [sourceRows, shape]; rfl
  have resident : InternedNestedProvenance.Edges heap rows := by
    intro row member
    have checked : heap.edgeRecords row.entry.key = some row := by
      have facts := (initial 0).1.semantic.ready.semantic.1.normal.facts
      exact InternedEdgeResidency.resident_edges heap facts.linked value (initial 0).2.1.resident row
        (by simpa only [shape, InternedEdgeResidency.nodeEdges] using member)
    exact checked
  have returned := SourceCurrentRawRebuildNumeric.modify formulas solver inventory entry rows rows depth free
    (before (bits + 2)) (initial_frame bits formulas solver) profile (initial_fits _) (shape ▸ (initial 0).2.1) resident
  have same := SourceCurrentAllocatedRawRebuild.modify_unchanged value sourceRows sourceRows (before (bits + 2)) rfl
  dsimp only at returned
  rw [← shape, ← originalRows, same] at returned
  exact ⟨same, returned.2.1, returned.2.2.1⟩

/-- Initial source probes construct a non-Cap Mu cleanup at the unchanged full caller and every fuel. -/
theorem constructed_terminal_mu (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ ∃ result,
      SourceCurrentNodeTerminalNumeric.Receipt formulas solver inventory profile 0 ⟨emptyField, recursive⟩
        (caller (bits + 2)) EndpointMemoGateTrace.empty result := by
  have available : Available heap recursive := available_values 0 recursive (by simp [values])
  have terminal : SourceCurrentNodeTerminalNumeric.Terminal recursive := by cbv; exact .binder
  obtain ⟨result, receipt⟩ := SourceCurrentNodeTerminalNumeric.complete formulas solver inventory 0 ⟨emptyField, recursive⟩
    (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver) profile (initial_fits _)
    (empty_ready 0) available terminal
  exact ⟨no_cap, result, receipt⟩

/-- Empty terminal execution needs no Room and retains the exact source-built caller. -/
theorem constructed_terminal_empty (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ result, SourceCurrentNodeTerminalNumeric.Receipt formulas solver inventory profile 0 ⟨emptyField, .empty⟩
      (caller (bits + 2)) EndpointMemoGateTrace.empty result :=
  SourceCurrentNodeTerminalNumeric.complete formulas solver inventory 0 ⟨emptyField, .empty⟩
    (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver) profile (initial_fits _)
    (empty_ready 0) (InternedProbeProvenance.empty_available heap) .empty

/-- An actual union with an open depth member stops at the exact full caller without a closure premise. -/
theorem constructed_terminal_open_union (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let built := run (makeUnion replacements) heap
    let checked := SourceCurrentAllocatedQueryMemo.advancePhysical (before (bits + 2)) ⟨built.2, operations⟩
    let state := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
    let numeric := SourceCurrentRawRebuildNumeric.constructorProfile replacements.length profile
    built.1.free ≠ [] ∧ ∃ result,
      SourceCurrentNodeTerminalNumeric.Receipt formulas solver inventory numeric 0 ⟨emptyField, built.1⟩ state
        EndpointMemoGateTrace.empty result := by
  let built := run (makeUnion replacements) heap
  have ready := (initial (bits + 2)).1
  have noMu := InternedShallowHeap.makeUnion_noNewMu replacements heap
  have simple := SourceEqualityNativeDemandHeapPrimitives.union replacements heap ready.semantic.ready replacement_available
  have semantic := SourceCurrentAllocatedNativeSemanticHeap.work_semantic (makeUnion replacements) heap ready.semantic
    (.union replacements replacement_available)
  have costs := InternedFreshOrdinaryCostHeap.preserve heap built.2 ready.costs noMu
  have fields := SourceCurrentAllocatedNativeCodeFields.makeUnion_heap operations replacements heap ready.good.fields
  have effects : SourceCurrentConjunctionRowsAllocation.Effects
      (SourceCurrentAllocatedNativeEffects.physical (before (bits + 2))) ⟨built.2, operations⟩ :=
    ⟨simple.1, ⟨semantic, costs, ready.good.operations, fields⟩, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  let checked := SourceCurrentAllocatedQueryMemo.advancePhysical (before (bits + 2)) ⟨built.2, operations⟩
  let state := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  let numeric := SourceCurrentRawRebuildNumeric.constructorProfile replacements.length profile
  have afterReady := SourceCurrentConjunctionClassScan.advance_ready (before (bits + 2)) _ ready effects
  have afterFrame := SourceCurrentConstrainedCapOperandFrame.advance (initial_frame bits formulas solver) afterReady
    (SourceCurrentAllocatedQueryMemo.advance_extension _ _ effects) rfl rfl
    (SourceCurrentConstrainedCapGuardHeap.preserve Plain heap built.2 guards noMu)
  have resources := SourceCurrentMemoMergeResourceControl.union replacements heap
    (SourceCurrentConstrainedCapTargetForecast.scalar profile) replacements.length
    (SourceCurrentMemoMergeResourceControl.initial heap (InternedValueMassHeap.initialBound heap)
      (InternedValueMassHeap.initial heap ready.good.native.machine.1)) replacement_available (Nat.le_refl _)
  have numericFits : Fits numeric checked :=
    ⟨resources.1.nodes, resources.1.edges, (initial_fits (bits + 2)).domains, resources.1.stored⟩
  have afterContext : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory state EndpointMemoGateTrace.empty :=
    ⟨afterReady, afterFrame.admitted, SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver checked
        SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
      SourceCurrentMemoMergeEffects.stored_empty built.2,
      (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty (SourceEqualityPCSGuard.holds formulas solver) ambient),
      SourceCurrentEmptinessMemo.empty_correct formulas solver built.2, EndpointMemoGateTrace.empty_valid built.2,
      InternedFreshOrdinaryProbeHeap.union replacements heap (context (bits + 2) formulas solver).probes⟩
  have terminal : SourceCurrentNodeTerminalNumeric.Terminal built.1 := by
    dsimp only [built]
    cbv
    exact .union
  have result := SourceCurrentNodeTerminalNumeric.complete formulas solver inventory 0 ⟨emptyField, built.1⟩ state
    EndpointMemoGateTrace.empty afterContext afterFrame numeric numericFits (empty_ready 0) simple.2 terminal
  exact ⟨by cbv; decide, result⟩

end MicroCFTA.RawTerminalIntegration
#check @MicroCFTA.RawTerminalIntegration.constructed_changed_raw
#print axioms MicroCFTA.RawTerminalIntegration.constructed_changed_raw
#check @MicroCFTA.RawTerminalIntegration.constructed_unchanged_raw
#print axioms MicroCFTA.RawTerminalIntegration.constructed_unchanged_raw
#check @MicroCFTA.RawTerminalIntegration.constructed_terminal_mu
#print axioms MicroCFTA.RawTerminalIntegration.constructed_terminal_mu
#check @MicroCFTA.RawTerminalIntegration.constructed_terminal_empty
#print axioms MicroCFTA.RawTerminalIntegration.constructed_terminal_empty
#check @MicroCFTA.RawTerminalIntegration.constructed_terminal_open_union
#print axioms MicroCFTA.RawTerminalIntegration.constructed_terminal_open_union
