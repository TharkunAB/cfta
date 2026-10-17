import MicroCFTA.SourceCurrentConstrainedCapOperandNumeric
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence
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

namespace MicroCFTA.OperandNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("a", .top) top [], .mk ("b", .top) top []],
  .node [.mk ("a", .top) top [], .mk ("c", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def seedEqualities : Option EqualityNormalize.Constraints := some [[[0], [1]]]
private def seedBuild := SourceEqualityConstraintAllocation.construct seedEqualities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok value => value
  | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def preparedOperations := (SourceEqualityConstraintMemoAllocation.descend seedValue 0 seedState).2
private def operations := SourceEqualityMkEdgeAllocation.emptyField preparedOperations

private theorem seed_cached : SourceEqualityGuardReadback.Cached seedEqualities := by
  have actual : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual

private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv

private theorem prepared_valid : SourceEqualityConstraintMemoAllocation.Valid preparedOperations := by
  obtain ⟨value, cache, built, cacheValid, ready, _steps, _read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete seedEqualities seed_cached Cache.emptyState Cache.empty_valid
  have same : value = seedValue := Except.ok.inj ((congrArg Prod.fst built).symm.trans seed_constructed)
  subst value
  have cacheSame : cache = seedBuild.2 := (congrArg Prod.snd built).symm
  subst cache
  exact (SourceEqualityConstraintMemoAllocation.descend_correct seedValue 0 seedState
    (SourceEqualityConstraintMemoAllocation.initial_valid _ cacheValid) ready).1
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good (width : Nat) : Good (before width) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) preparedOperations
    prepared_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))

private theorem node_ready : NodeReady machine request := ⟨empty_domain machine, originals.1, originals.2⟩

private def row : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("unused", .top) top []) empty).1
private def candidate : Value Symbol Guard := (run (makeNode [row]) heap).1
private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private noncomputable def afterFirst (width : Nat) : Checked width := (execute 8 nodeControl (before width)).state

private theorem evaluated (width : Nat) : execute 8 nodeControl (before width) = .done candidate (afterFirst width) := by
  set_option cbv.maxSteps 200000000 in cbv

private theorem candidate_absent : SourcePreparedSharedRows.read heap 3 = none := by cbv
private theorem operation_record : ∃ cell,
    operations.descents (seedValue.identity, 0) = some cell ∧
      SourceEqualityConstraintMemoAllocation.DescendGood operations.constraints (seedValue.identity, 0) cell := by
  have present : (operations.descents (seedValue.identity, 0)).isSome = true := by cbv
  cases found : operations.descents (seedValue.identity, 0) with
  | none => rw [found] at present; cases present
  | some cell => exact ⟨cell, rfl, (SourceEqualityMkEdgeAllocation.emptyField_correct preparedOperations prepared_valid).1.descents _ _ found⟩

private theorem candidate_input : SourceRecursiveIntersectionInputView.inputOf candidate = .node 3 := by cbv

private theorem candidate_outside : SourceRecursiveIntersectionInputView.inputOf candidate ∉
    SourceRecursiveIntersectionInputView.inventory heap := by
  rw [candidate_input]
  have count : heap.nodes.next = 3 := by cbv
  simp only [SourceRecursiveIntersectionInputView.inventory, count]
  decide

private theorem initial_semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed

private theorem initial_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
  simpa only [built, heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain expression

private theorem initial_ready (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) := by
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  exact ⟨initial_good width, initial_semantic, costs,
    SourceCurrentAllocatedNativeScopeCache.initial_scoped width machine,
    SourceRecursiveIntersectionNative.idle_initial machine⟩

private theorem initial_caps : SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 left ∧
    SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 right := by
  constructor
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member

private theorem initial_closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv

private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap
    (initial_good 0).native.machine.1 left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left heap (initial_good 0).native.machine.1.coherent
      originals.1 initial_closed.1)
    (SourceRecursiveIntersectionOriginalOutput.closed_original right heap (initial_good 0).native.machine.1.coherent
      originals.2 initial_closed.2)
    originals.1 originals.2 initial_closed.1 initial_closed.2

private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩

private theorem initial_fits (width : Nat) : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial_good width).native.machine.1⟩

private theorem initial_pool (width : Nat) : SourceCurrentConstrainedCapGeneratedQuerySequence.Pool 1 [left, right] (before width) := by
  constructor
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact originals.1
    · exact originals.2
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact initial_closed.1
    · exact initial_closed.2
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact initial_caps.1
    · exact initial_caps.2


open InternedNestedProvenance (Values)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentAllocatedTargetGraph (Operand)
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "numWork" => SourceCurrentConstrainedCapOperandNumeric.workFuel
local notation "numSelection" => SourceCurrentConstrainedCapOperandNumeric.selectionFuel
local notation "numRead" => SourceCurrentProjectionNumeric.readFuel
local notation "projectWork" => SourceCurrentProjectionNumeric.workFuel
local notation "clear" => SourceCurrentAllocatedMerge.literalClear

private def inputs : List (Value Symbol Guard) := [left, right, .reference .depth]
private def resource := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next profile.mass
private theorem scalar_fits (width : Nat) : Fits resource (before width).native.machine.heap :=
  SourceCurrentMemoMergeResourceControl.initial heap profile.mass
    (InternedValueMassHeap.initial heap (initial_good width).native.machine.1)
private theorem input_available (width : Nat) : Values (before width).native.machine.heap inputs := by
  intro value member
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact originals.1
  · exact originals.2
  · exact InternedNestedProvenance.depth_available _
private theorem first_domain : Domain [0] inputs := by
  simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
    SourceEqualityProjectionGraph.select, inputs] using initial_closed.1
private theorem second_domain : Domain [1] inputs := by
  simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
    SourceEqualityProjectionGraph.select, inputs] using initial_closed.2
private theorem open_input : ¬MergedColdReaderClosedInputs.ClosedValues inputs := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [inputs])
  cases impossible
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : Memo) := by
  intro ambient key entry absent
  cases absent

/-- Initial constructed physical facts produce one full numeric Operand beside an open unselected root. -/
theorem constructed_operand (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
    ∃ result after saved final,
      Operand [0] inputs (before width) SourceCurrentMemoMergeGraph.empty result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] inputs
        (before width) SourceCurrentMemoMergeGraph.empty result after saved EndpointMemoGateTrace.empty final ∧
      Frame formulas solver inventory after ∧ Fits (numWork [0] inputs.length resource) after.native.machine.heap ∧
      ∃ projected, ∃ middle : Checked width,
        SourceEqualityProjectionWorker.forest (projectWork [0]) (numRead [0] inputs.length resource)
          [0] inputs heap = .done projected middle.native.machine.heap ∧
        SourceCurrentMemoMergeWorker.call clear top (numWork [0] inputs.length resource)
          (numSelection [0] inputs.length resource) projected middle.native.machine.heap SourceCurrentMemoMergeGraph.empty =
          .done result after.native.machine.heap saved ∧
        after.native.nodes = (before width).native.nodes ∧ after.native.edges = (before width).native.edges ∧
        EndpointMemoGateTrace.Valid after.native.machine.heap final ∧
        ∃ cell, after.operations.descents (seedValue.identity, 0) = some cell ∧
          SourceEqualityConstraintMemoAllocation.DescendGood after.operations.constraints (seedValue.identity, 0) cell := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready width) initial_guards rfl
  obtain ⟨result, after, saved, final, actual, receipt, returned, fits, _mass,
    projected, middle, _current, _projection, _merged, _middleFits, projectedDone, mergedDone, _projectStable, _mergeStable⟩ :=
    SourceCurrentConstrainedCapOperandNumeric.complete formulas solver inventory [0] inputs (before width)
      SourceCurrentMemoMergeGraph.empty resource frame (input_available width) first_domain
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) (scalar_fits width)
  obtain ⟨cell, found, _valid⟩ := operation_record
  have finalFound := receipt.effects.grows.descents _ _ found
  exact ⟨open_input, result, after, saved, final, actual, receipt, returned, fits,
    projected, middle, projectedDone, mergedDone, receipt.nodes, receipt.edges, receipt.globals,
    cell, finalFound, returned.ready.good.operations.descents _ _ finalFound⟩

/-- The second complete Operand receives only the first call's own exact returned resources and tables. -/
theorem constructed_serial (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ first middle firstMemo firstGlobals result after saved final,
      Operand [0] inputs (before width) SourceCurrentMemoMergeGraph.empty first middle firstMemo ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] inputs
        (before width) SourceCurrentMemoMergeGraph.empty first middle firstMemo EndpointMemoGateTrace.empty firstGlobals ∧
      Frame formulas solver inventory middle ∧ Fits (numWork [0] inputs.length resource) middle.native.machine.heap ∧
      Operand [1] inputs middle firstMemo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [1] inputs
        middle firstMemo result after saved firstGlobals final ∧ Frame formulas solver inventory after ∧
      Fits (numWork [1] inputs.length (numWork [0] inputs.length resource)) after.native.machine.heap ∧
      ∃ projected, ∃ reached : Checked width,
        SourceEqualityProjectionWorker.forest (projectWork [1]) (numRead [1] inputs.length (numWork [0] inputs.length resource))
          [1] inputs middle.native.machine.heap = .done projected reached.native.machine.heap ∧
        SourceCurrentMemoMergeWorker.call clear top (numWork [1] inputs.length (numWork [0] inputs.length resource))
          (numSelection [1] inputs.length (numWork [0] inputs.length resource)) projected reached.native.machine.heap firstMemo =
          .done result after.native.machine.heap saved ∧
        after.native.nodes = (before width).native.nodes ∧ after.native.edges = (before width).native.edges ∧
        Values after.native.machine.heap inputs ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready width) initial_guards rfl
  obtain ⟨first, middle, firstMemo, firstGlobals, firstRun, firstReceipt, firstFrame, firstFits, _firstMass, _firstSchedule⟩ :=
    SourceCurrentConstrainedCapOperandNumeric.complete formulas solver inventory [0] inputs (before width)
      SourceCurrentMemoMergeGraph.empty resource frame (input_available width) first_domain
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) (scalar_fits width)
  obtain ⟨result, after, saved, final, actual, receipt, returned, fits, _mass,
    projected, reached, _current, _projection, _merged, _middleFits, projectedDone, mergedDone, _projectStable, _mergeStable⟩ :=
    SourceCurrentConstrainedCapOperandNumeric.complete formulas solver inventory [1] inputs middle firstMemo
      (numWork [0] inputs.length resource) firstFrame firstReceipt.originals second_domain firstReceipt.stored
      firstReceipt.covered firstGlobals firstReceipt.globals firstFits
  exact ⟨first, middle, firstMemo, firstGlobals, result, after, saved, final,
    firstRun, firstReceipt, firstFrame, firstFits, actual, receipt, returned, fits,
    projected, reached, projectedDone, mergedDone, receipt.nodes.trans firstReceipt.nodes,
    receipt.edges.trans firstReceipt.edges, receipt.originals, receipt.globals⟩

private def generatedResource := SourceCurrentMemoMergeResourceControl.initialBound
  (SourceCurrentAllocatedNativeResourceForecast.step profile).nodes
  (SourceCurrentAllocatedNativeResourceForecast.step profile).edges
  (SourceCurrentAllocatedNativeResourceForecast.step profile).mass

/-- An initial forecast constructs a new native result, then numeric Operand work retains its populated cells. -/
theorem generated_then_numeric (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits profile) :
    ∃ next fuel,
      SourceCurrentConstrainedCapGeneratedQueryResources.Receipt profile 1 formulas solver next fuel left right
        (before (bits + 2)) candidate (afterFirst (bits + 2)) EndpointMemoGateTrace.empty ∧
      SourceRecursiveIntersectionInputView.inputOf candidate ∉ SourceRecursiveIntersectionInputView.inventory heap ∧
      ∃ result after saved final,
        Operand [0] [candidate, .reference .depth] (afterFirst (bits + 2)) SourceCurrentMemoMergeGraph.empty result after saved ∧
        SourceCurrentAllocatedMergeOperand.Receipt formulas solver next [0] [candidate, .reference .depth]
          (afterFirst (bits + 2)) SourceCurrentMemoMergeGraph.empty result after saved EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after ∧ Fits (numWork [0] 2 generatedResource) after.native.machine.heap ∧
        (afterFirst (bits + 2)).native.nodes.cells 0 = some ⟨request, .returned candidate⟩ ∧
        (afterFirst (bits + 2)).native.edges.cells 0 = some ⟨⟨IntersectionEmptyDomain.emptyDomain, row, row⟩, .returned row⟩ ∧
        after.native.nodes = (afterFirst (bits + 2)).native.nodes ∧ after.native.edges = (afterFirst (bits + 2)).native.edges ∧
        ∃ projected, ∃ middle : Checked (bits + 2),
          SourceEqualityProjectionWorker.forest (projectWork [0]) (numRead [0] 2 generatedResource)
            [0] [candidate, .reference .depth] (afterFirst (bits + 2)).native.machine.heap =
              .done projected middle.native.machine.heap ∧
          SourceCurrentMemoMergeWorker.call clear top (numWork [0] 2 generatedResource) (numSelection [0] 2 generatedResource)
            projected middle.native.machine.heap SourceCurrentMemoMergeGraph.empty = .done result after.native.machine.heap saved ∧
          ∃ cell, after.operations.descents (seedValue.identity, 0) = some cell ∧
            SourceEqualityConstraintMemoAllocation.DescendGood after.operations.constraints (seedValue.identity, 0) cell := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready (bits + 2)) initial_guards rfl
  obtain ⟨next, fuel, value, queried, query⟩ := SourceCurrentConstrainedCapGeneratedQueryResources.complete
    profile 1 formulas solver inventory (before (bits + 2)) frame (initial_fits (bits + 2)) room left right
    originals.1 originals.2 initial_closed.1 initial_closed.2 initial_caps.1 initial_caps.2
    EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique _ 8 nodeControl
    (before (bits + 2)) _ (afterFirst (bits + 2)) _ candidate query.joint.done (evaluated (bits + 2))
  have fits : Fits generatedResource (afterFirst (bits + 2)).native.machine.heap := by
    refine ⟨query.fits.stored.mono ?_, ?_, ?_, Nat.zero_le _⟩
    · unfold generatedResource SourceCurrentMemoMergeResourceControl.initialBound
      omega
    · exact Nat.le_trans query.fits.nodes (by unfold generatedResource SourceCurrentMemoMergeResourceControl.initialBound; omega)
    · exact Nat.le_trans query.fits.edges (by unfold generatedResource SourceCurrentMemoMergeResourceControl.initialBound; omega)
  have available : Values (afterFirst (bits + 2)).native.machine.heap [candidate, .reference .depth] := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact query.query.available
    · exact InternedNestedProvenance.depth_available _
  have domain : Domain [0] [candidate, .reference .depth] := by
    simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select] using query.query.closed
  obtain ⟨result, after, saved, final, actual, receipt, returned, finalFits, _mass,
    projected, middle, _current, _projection, _merged, _middleFits, projectedDone, mergedDone, _projectStable, _mergeStable⟩ :=
    SourceCurrentConstrainedCapOperandNumeric.complete formulas solver next [0] [candidate, .reference .depth]
      (afterFirst (bits + 2)) SourceCurrentMemoMergeGraph.empty generatedResource query.frame available domain
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty query.query.globals fits
  obtain ⟨cell, found, _valid⟩ := operation_record
  have queriedFound := query.query.effects.grows.descents _ _ found
  have finalFound := receipt.effects.grows.descents _ _ queriedFound
  refine ⟨next, fuel, query, candidate_outside, result, after, saved, final, actual, receipt, returned, finalFits,
    ?_, ?_, receipt.nodes, receipt.edges, projected, middle, projectedDone, mergedDone,
    cell, finalFound, returned.ready.good.operations.descents _ _ finalFound⟩
  · set_option cbv.maxSteps 200000000 in cbv
  · set_option cbv.maxSteps 200000000 in cbv

end MicroCFTA.OperandNumericIntegration

#print axioms MicroCFTA.OperandNumericIntegration.constructed_operand
#check @MicroCFTA.OperandNumericIntegration.constructed_operand
#print axioms MicroCFTA.OperandNumericIntegration.constructed_serial
#check @MicroCFTA.OperandNumericIntegration.constructed_serial
#print axioms MicroCFTA.OperandNumericIntegration.generated_then_numeric
#check @MicroCFTA.OperandNumericIntegration.generated_then_numeric
