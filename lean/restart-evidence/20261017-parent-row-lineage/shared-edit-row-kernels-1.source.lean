import MicroCFTA.SourceCurrentSharedEditRowLineage
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

namespace MicroCFTA.SharedEditRowIntegration
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

open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentEditDomains
local notation "M" => EndpointMemoGateSource.empty

private def childEdits : SourceEqualityEdits.Edits EqualityNormalize.Path := .editBelow [(0, .editAt [0])]
private def entries : List (Int × SourceEqualityEdits.Edits EqualityNormalize.Path) := [(3, childEdits)]
private def firstEdge := run (makeEdge ("first", .top) parentGuard inputs) heap
private def firstState (width : Nat) := advanceHeap (start width) firstEdge.2
private def secondEdge := run (makeEdge ("second", .top) parentGuard inputs) firstEdge.2
private def secondState (width : Nat) := advanceHeap (firstState width) secondEdge.2
private def deadEdge := run (makeEdge ("dead", .top) parentGuard (inputs ++ [.empty])) secondEdge.2
private def sourceState (width : Nat) := advanceHeap (secondState width) deadEdge.2
private def sourceRows := [secondEdge.1, deadEdge.1, firstEdge.1, secondEdge.1]

private theorem short_children (width : Nat) (state : Shared width) :
    EditChildren record inputs entries 0 inputs state inputs state :=
  .unselected 0 rfl (.unselected 1 rfl (.unselected 2 rfl .nil))

private theorem short_reads (width : Nat) (state : Shared width)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ChildrenReads formulas solver heap (short_children width state) M M :=
  .unselected (.unselected (.unselected .nil))

private theorem long_children (width : Nat) (state : Shared width) :
    EditChildren record inputs entries 0 (inputs ++ [.empty]) state (inputs ++ [.empty]) state :=
  .unselected 0 rfl (.unselected 1 rfl (.unselected 2 rfl (.selected 3 rfl .empty .nil)))

private theorem long_reads (width : Nat) (state : Shared width)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ChildrenReads formulas solver heap (long_children width state) M M :=
  .unselected (.unselected (.unselected (.selected .empty .nil)))

private theorem edge_children : firstEdge.1.children = inputs ∧ secondEdge.1.children = inputs ∧
    deadEdge.1.children = inputs ++ [.empty] := by cbv

private theorem source_ready (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SharedReady formulas solver inventory record inputs heap (sourceState width) ∧
      InternedNestedProvenance.Edges (sourceState width).checked.native.machine.heap sourceRows := by
  have one := edge_physical (start_ready width formulas solver) ("first", .top) parentGuard inputs
    parent_field (input_available width)
  have two := edge_physical one.1 ("second", .top) parentGuard inputs parent_field
    (fun value member => one.2.1.keeps.available value (input_available width value member))
  have three := edge_physical two.1 ("dead", .top) parentGuard (inputs ++ [.empty]) parent_field (by
    intro value member
    rcases List.mem_append.mp member with member | member
    · exact two.2.1.keeps.available value (one.2.1.keeps.available value (input_available width value member))
    · have same : value = .empty := List.mem_singleton.mp member
      subst value
      exact .empty _)
  refine ⟨three.1, ?_⟩
  intro row member
  simp only [sourceRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact InternedEdgeResidency.edge_grows _ _ three.2.1.keeps.growth _ two.2.2.1
  · exact three.2.2.1
  · exact InternedEdgeResidency.edge_grows _ _ (two.2.1.trans three.2.1).keeps.growth _ one.2.2.1
  · exact InternedEdgeResidency.edge_grows _ _ three.2.1.keeps.growth _ two.2.2.1

private def rowWork (width : Nat) (row : EdgeValue Symbol Guard) (state : Shared width) :=
  run (makeEdge row.entry.key.symbol row.entry.key.constraint row.children) state.checked.native.machine.heap
private def rawFirst (width : Nat) := rowWork width secondEdge.1 (sourceState width)
private def rawState1 (width : Nat) := advanceHeap (sourceState width) (rawFirst width).2
private def rawSecond (width : Nat) := rowWork width deadEdge.1 (rawState1 width)
private def rawState2 (width : Nat) := advanceHeap (rawState1 width) (rawSecond width).2
private def rawThird (width : Nat) := rowWork width firstEdge.1 (rawState2 width)
private def rawState3 (width : Nat) := advanceHeap (rawState2 width) (rawThird width).2
private def rawFourth (width : Nat) := rowWork width secondEdge.1 (rawState3 width)
private def rawAfter (width : Nat) := advanceHeap (rawState3 width) (rawFourth width).2
private def rawRows (width : Nat) := [(rawFirst width).1, (rawSecond width).1, (rawThird width).1, (rawFourth width).1]

private theorem actual_rows (width : Nat) :
    EditRows record inputs entries sourceRows (sourceState width) (rawRows width) (rawAfter width) := by
  refine .cons ?_ rfl (.cons ?_ rfl (.cons ?_ rfl (.cons ?_ rfl .nil)))
  · simpa only [edge_children.2.1] using short_children width (sourceState width)
  · simpa only [edge_children.2.2] using long_children width (rawState1 width)
  · simpa only [edge_children.1] using short_children width (rawState2 width)
  · simpa only [edge_children.2.1] using short_children width (rawState3 width)

private theorem actual_reads (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    RowsReads formulas solver heap (actual_rows width) M M := by
  exact .cons (short_reads width (sourceState width) formulas solver)
    (.cons (long_reads width (rawState1 width) formulas solver)
      (.cons (short_reads width (rawState2 width) formulas solver)
        (.cons (short_reads width (rawState3 width) formulas solver) .nil)))

private theorem populated : Populated (.editBelow entries) := by
  simp [Populated, entries, childEdits, HasLeaf, SourceEqualityEditLeafPaths.leaves]
private theorem allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow entries) := by
  simp [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All, entries, childEdits, record_paths]
private theorem rows_safe : RowsSafe entries sourceRows := by
  intro row member query edit found value selected
  have query_eq : query = 3 := by
    simp [entries, SourceEqualityNeededMap.lookup] at found
    omega
  subst query
  have edit_eq : edit = childEdits := by simpa [entries, SourceEqualityNeededMap.lookup] using found
  subst edit
  simp only [sourceRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [edge_children.2.1] at selected
    simp [inputs] at selected
  · rw [edge_children.2.2] at selected
    have same : value = .empty := by simpa [inputs] using selected.symm
    subst value
    intro path action retained
    simp [SourceEqualityProjectionPathDomain.NodeClosed]
  · rw [edge_children.1] at selected
    simp [inputs] at selected
  · rw [edge_children.2.1] at selected
    simp [inputs] at selected

private def finalNode (width : Nat) := run (makeNode (rawRows width)) (rawAfter width).checked.native.machine.heap

end MicroCFTA.SharedEditRowIntegration

