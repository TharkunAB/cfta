import MicroCFTA.SourceCurrentClassPassPhaseLineage
import MicroCFTA.SourceCurrentClassPassNumeric
import MicroCFTA.SourceCurrentConstrainedCapClassPassNumeric
import MicroCFTA.SourceCurrentConstrainedCapClassNumeric
import MicroCFTA.SourceCurrentConstrainedCapEditNumeric
import MicroCFTA.SourceCurrentConstrainedCapEditListNumeric
import MicroCFTA.SourceCurrentConstrainedCapEditFrame
import MicroCFTA.SourceCurrentConstrainedCapEditForecast
import MicroCFTA.SourceCurrentConstrainedCapMixedShared
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
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
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ClassPhaseLineageIntegration
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

private theorem operation_record : ∃ cell,
    operations.descents (seedValue.identity, 0) = some cell ∧
      SourceEqualityConstraintMemoAllocation.DescendGood operations.constraints (seedValue.identity, 0) cell := by
  have present : (operations.descents (seedValue.identity, 0)).isSome = true := by cbv
  cases found : operations.descents (seedValue.identity, 0) with
  | none => rw [found] at present; cases present
  | some cell => exact ⟨cell, rfl, (SourceEqualityMkEdgeAllocation.emptyField_correct preparedOperations prepared_valid).1.descents _ _ found⟩

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

local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "MixedStored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "QueryFits" => SourceCurrentConstrainedCapGeneratedQueryResources.Fits
private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0], [1]] with
  | some value => value
  | none => ⟨.empty, []⟩
private theorem record_built : SourceEqualityClassOrder.recordOf [[0], [1]] = some record := by cbv
private theorem record_paths : record.paths = [[0], [1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual, done, coherent, _paths⟩ :=
    SourceEqualityClassOrder.recordOf_complete [[0], [1]]
      ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0, .terminal), (1, .terminal)], by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans record_built)
  exact same ▸ coherent
private theorem record_active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0], by simp, [1], by simp, by decide⟩
private theorem member : [0] ∈ record.paths := by rw [record_paths]; simp
private theorem domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) inputs := by
  intro path present
  rw [record_paths] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact first_domain
  · exact second_domain
private theorem input_caps : ∀ value ∈ inputs, Cap 1 value := by
  intro value present
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact initial_caps.1
  · exact initial_caps.2
  · exact .plain 1 (.reference .depth)
private def start (width : Nat) : Shared width :=
  SourceCurrentAllocatedSharedTargetState.initial (before width) SourceCurrentMemoMergeGraph.empty
private theorem start_ready (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SharedReady formulas solver inventory record inputs heap (start width) := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready width) initial_guards rfl
  exact SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs heap
    (before width) SourceCurrentMemoMergeGraph.empty (initial_ready width) frame.admitted
    (SourceEqualityRequiredCache.pure_keeps heap initial_semantic.ready)
    (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
private theorem start_stored (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : MixedStored record inputs (start width) := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready width) initial_guards rfl
  exact SourceCurrentConstrainedCapMixedShared.initial_stored record inputs (before width) SourceCurrentMemoMergeGraph.empty
    (SourceCurrentConstrainedCapOperandFrame.current frame)
    (SourceCurrentConstrainedCapMemoMerge.stored_empty Plain)
private theorem initially_missing (width : Nat) : (start width).targets [0] = none := rfl

private def parentGuard : Guard := ⟨seedEqualities, .top⟩
private theorem parent_field : SourceCurrentConjunctionEquality.FieldAvailable operations parentGuard := by
  refine ⟨seed_cached, ⟨seedValue, .top⟩, ?_⟩
  cbv

private def parentEdge := run (makeEdge ("parent", .top) parentGuard inputs) heap
private def edgeState (width : Nat) := SourceCurrentAllocatedSharedEditGraph.advanceHeap (start width) parentEdge.2
private def parentWork := run (makeNode [parentEdge.1]) parentEdge.2
private def parent := parentWork.1
private def parentState (width : Nat) := SourceCurrentAllocatedSharedEditGraph.advanceHeap (edgeState width) parentWork.2
private def edgeProfile := SourceCurrentConstrainedCapEditFrame.constructorProfile inputs.length profile
private def parentProfile := SourceCurrentConstrainedCapEditFrame.constructorProfile 1 edgeProfile
private def edits : SourceEqualityEdits.Edits EqualityNormalize.Path := SourceEqualityEdits.build [([0], [0])]

private theorem edits_literal : edits = .editBelow [(0, .editAt [0])] := by cbv
private theorem parent_children : children parent = inputs := by cbv
private theorem parent_rows : nodeEdges parent = [parentEdge.1] := by cbv
private theorem parent_open : parent.free ≠ [] := by
  cbv
  intro impossible
  cases impossible
private theorem parentEdge_children : parentEdge.1.children = inputs := by cbv

private theorem parent_invariants (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (parentState width).checked ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits parentProfile (parentState width).checked ∧
      SharedReady formulas solver inventory record inputs heap (parentState width) ∧
      MixedStored record inputs (parentState width) ∧ Available parentWork.2 parent ∧ Cap 2 parent ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical (start width).checked)
        (SourceCurrentAllocatedNativeEffects.physical (parentState width).checked) := by
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready width) initial_guards rfl
  have edge := SourceCurrentConstrainedCapEditFrame.edge profile inputs.length frame (initial_fits width)
    (start_ready width formulas solver) ("parent", .top) parentGuard inputs parent_field (input_available width)
    (Nat.le_refl _) (start_stored width formulas solver)
  have resident : InternedNestedProvenance.Edges parentEdge.2 [parentEdge.1] := by
    intro row member
    exact (List.mem_singleton.mp member) ▸ edge.2.2.2.2.2.1
  have node := SourceCurrentConstrainedCapEditFrame.node edgeProfile 1 edge.1 edge.2.1 edge.2.2.2.1
    [parentEdge.1] resident (Nat.le_refl _) edge.2.2.1
  have rowCap : ∀ row ∈ [parentEdge.1], SourceCurrentConstrainedCap.Edge Plain 2 row := by
    intro row member
    have same : row = parentEdge.1 := List.mem_singleton.mp member
    subst row
    intro child selected
    rw [parentEdge_children] at selected
    exact input_caps child selected
  have facts := edge.2.2.2.1.checked.good.native.machine.1
  have bounded := SourceCurrentConstrainedCap.makeNode Plain 2 [parentEdge.1] parentEdge.2
    facts.coherent facts.linked resident rowCap
  exact ⟨node.1, node.2.1, node.2.2.2.1, node.2.2.1, node.2.2.2.2.2, bounded,
    edge.2.2.2.2.1.trans node.2.2.2.2.1⟩

private theorem parent_selected : SourceEqualityProjectionPathDomain.NodeClosed [0] parent := by
  cbv
  simp [SourceEqualityProjectionGraph.select, EdgeValue.children, SourceEqualityProjectionPathDomain.NodeClosed, Value.free]

private theorem edits_safe : SourceCurrentEditDomains.Safe edits parent := by
  rw [edits_literal]
  intro path action retained
  simp only [SourceEqualityEditLeafPaths.leaves, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil, List.mem_singleton, Prod.mk.injEq] at retained
  rcases retained with ⟨rfl, rfl⟩
  exact parent_selected

private theorem edits_populated : SourceCurrentEditDomains.Populated edits := by
  rw [edits_literal]
  simp [SourceCurrentEditDomains.Populated, SourceCurrentEditDomains.HasLeaf,
    SourceEqualityEditLeafPaths.leaves]

private theorem edits_nonempty : SourceCurrentEditDomains.HasLeaf edits := by
  refine ⟨[0], [0], ?_⟩
  rw [edits_literal]
  simp [SourceEqualityEditLeafPaths.leaves]

private theorem edits_allowed : SourceEqualitySharedEditEffects.Allowed record edits := by
  rw [edits_literal]
  simp [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All, record_paths]

private theorem parent_nonhereditary : ¬Cap 0 parent := by
  intro bounded
  have row := SourceCurrentHereditaryConstructors.node_edge (bounded.annotated rfl)
    parentEdge.1 (by rw [parent_rows]; simp)
  have invalid : ¬Plain parentEdge.1.entry.key.constraint := by cbv
  exact invalid row.1


private def selectedRecord : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] with
  | some value => value
  | none => ⟨.empty, []⟩
private theorem selected_built : SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] = some selectedRecord := by cbv
private theorem selected_paths : selectedRecord.paths = [[0, 0], [0, 1]] := by cbv
private theorem selected_coherent : SourceEqualityClassOrder.Coherent selectedRecord := by
  obtain ⟨actual, done, coherent, _paths⟩ :=
    SourceEqualityClassOrder.recordOf_complete [[0, 0], [0, 1]]
      ((EqualityTrie.toPathTrie_succeeds_iff _).mp
        ⟨.branch [(0, .branch [(0, .terminal), (1, .terminal)])], by cbv⟩)
  have same : actual = selectedRecord := Option.some.inj (done.symm.trans selected_built)
  exact same ▸ coherent
private theorem selected_active : EqualityNormalize.Nontrivial selectedRecord.paths := by
  rw [selected_paths]
  exact ⟨[0, 0], by simp, [0, 1], by simp, by decide⟩

private def forest : List (Value Symbol Guard) := [parent]
private theorem parent_selected_right : SourceEqualityProjectionPathDomain.NodeClosed [1] parent := by
  cbv
  simp [SourceEqualityProjectionGraph.select, EdgeValue.children, SourceEqualityProjectionPathDomain.NodeClosed, Value.free]
private theorem selected_domains : ∀ path ∈ selectedRecord.paths, Domain (path.map Int.ofNat) forest := by
  intro path retained
  rw [selected_paths] at retained
  simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with rfl | rfl
  · change ∀ value, SourceEqualityProjectionGraph.select [parent] 0 = some value →
      SourceEqualityProjectionPathDomain.NodeClosed [0] value
    intro value found
    have same : parent = value := Option.some.inj found
    cases same
    exact parent_selected
  · change ∀ value, SourceEqualityProjectionGraph.select [parent] 0 = some value →
      SourceEqualityProjectionPathDomain.NodeClosed [1] value
    intro value found
    have same : parent = value := Option.some.inj found
    cases same
    exact parent_selected_right
private theorem forest_open : ¬MergedColdReaderClosedInputs.ClosedValues forest := by
  intro closed
  exact parent_open (closed parent List.mem_cons_self)
private theorem parent_equalities : ∃ edge ∈ nodeEdges parent,
    edge.entry.key.constraint.equalities = some [[[0], [1]]] := by
  refine ⟨parentEdge.1, ?_, ?_⟩
  · rw [parent_rows]
    exact List.mem_cons_self
  · cbv

private noncomputable def classCeiling :=
  SourceCurrentConstrainedCapClassForecast.classProfile selectedRecord forest.length parentProfile
private noncomputable def classFuel :=
  SourceCurrentConstrainedCapClassForecast.classFuel selectedRecord forest.length parentProfile

private def records := [selectedRecord, selectedRecord, selectedRecord]
private theorem records_coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  have same : own = selectedRecord := by
    simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_coherent
private theorem records_active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = selectedRecord := by
    simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_active
private theorem records_domains : ∀ own ∈ records, ∀ path ∈ own.paths, Domain (path.map Int.ofNat) forest := by
  intro own member
  have same : own = selectedRecord := by
    simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_domains
private noncomputable def ceiling :=
  SourceCurrentConstrainedCapClassForecast.foldProfile records forest.length parentProfile

open SourceCurrentAllocatedClassPass (Fold FoldReads)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid

private theorem constructed_three_occurrences_proof (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits results after saved final,
    ∃ actual : Fold records forest (parentState (bits + 2)).checked SourceCurrentMemoMergeGraph.empty results after saved,
      FoldReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      ¬MergedColdReaderClosedInputs.ClosedValues forest ∧ records.length = 3 ∧
      ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
      ∃ tail : Fold (records.drop 2) forest (parentState (bits + 2)).checked
          SourceCurrentMemoMergeGraph.empty phaseValues phaseState phaseMemo,
      ∃ call : Class selectedRecord phaseValues phaseState phaseMemo headValues headState headMemo,
      ∃ later : Fold (records.take 1) headValues headState headMemo results after saved,
        FoldReads formulas solver tail EndpointMemoGateTrace.empty phaseMemos ∧
        ClassReads formulas solver call phaseMemos headMemos ∧
        FoldReads formulas solver later headMemos final ∧
        Ready phaseState ∧ Ready headState ∧
        Valid phaseState.native.machine.heap phaseMemos ∧ Valid headState.native.machine.heap headMemos ∧
        History phaseState ∧ History headState ∧ History after ∧
        Grows (parentState (bits + 2)).checked.native.machine.heap phaseState.native.machine.heap ∧
        Grows phaseState.native.machine.heap after.native.machine.heap := by
  obtain ⟨bits, room⟩ := exists_room ceiling
  have initial := parent_invariants (bits + 2) formulas solver
  have available : InternedNestedProvenance.Values (parentState (bits + 2)).checked.native.machine.heap forest := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ initial.2.2.2.2.1
  have reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records forest.length parentProfile := room
  obtain ⟨results, after, saved, _next, final, actual, reads, _receipt, _frame, _fits, _length, _done, _stable⟩ :=
    SourceCurrentClassPassNumeric.fold formulas solver inventory records records_coherent records_active forest
      (parentState (bits + 2)).checked SourceCurrentMemoMergeGraph.empty parentProfile initial.1 initial.2.1
      available records_domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) reserved
  have history : History (parentState (bits + 2)).checked :=
    .advance (.initial machine operations) ⟨parentWork.2, operations⟩ initial.2.2.2.2.2.2.keeps.growth
  obtain ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
      tail, call, later, _phaseInventory, _headInventory, _finalInventory,
      tailReads, callReads, laterReads, tailReceipt, callReceipt, _laterReceipt,
      phaseHistory, headHistory, finalHistory, firstGrowth, lastGrowth⟩ :=
    SourceCurrentClassPassPhaseLineage.fold_phase reads inventory records_coherent records_active
      initial.1.ready initial.1.admitted available records_domains (SourceCurrentMemoMergeEffects.stored_empty _)
      (empty_covered formulas solver) (EndpointMemoGateTrace.empty_valid _) history
      (index := 1) (record := selectedRecord) rfl
  exact ⟨bits, results, after, saved, final, actual, reads, forest_open, rfl,
    phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
    tail, call, later, tailReads, callReads, laterReads, tailReceipt.ready, callReceipt.ready,
    tailReceipt.globals.valid, callReceipt.globals.valid, phaseHistory, headHistory, finalHistory,
    firstGrowth, lastGrowth⟩

/-- A source-built open constrained forest produces the middle occurrence of a three-class right fold. -/
theorem constructed_three_occurrences (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits results after saved final,
    ∃ actual : Fold records forest (parentState (bits + 2)).checked SourceCurrentMemoMergeGraph.empty results after saved,
      FoldReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      ¬MergedColdReaderClosedInputs.ClosedValues forest ∧ records.length = 3 ∧
      ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
      ∃ tail : Fold (records.drop 2) forest (parentState (bits + 2)).checked
          SourceCurrentMemoMergeGraph.empty phaseValues phaseState phaseMemo,
      ∃ call : Class selectedRecord phaseValues phaseState phaseMemo headValues headState headMemo,
      ∃ later : Fold (records.take 1) headValues headState headMemo results after saved,
        FoldReads formulas solver tail EndpointMemoGateTrace.empty phaseMemos ∧
        ClassReads formulas solver call phaseMemos headMemos ∧
        FoldReads formulas solver later headMemos final ∧
        Ready phaseState ∧ Ready headState ∧
        Valid phaseState.native.machine.heap phaseMemos ∧ Valid headState.native.machine.heap headMemos ∧
        History phaseState ∧ History headState ∧ History after ∧
        Grows (parentState (bits + 2)).checked.native.machine.heap phaseState.native.machine.heap ∧
        Grows phaseState.native.machine.heap after.native.machine.heap :=
  constructed_three_occurrences_proof formulas solver

#check @constructed_three_occurrences
#print constructed_three_occurrences
#print axioms constructed_three_occurrences
end MicroCFTA.ClassPhaseLineageIntegration

