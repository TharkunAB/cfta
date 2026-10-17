import MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete
import MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
import MicroCFTA.SourceCurrentRequiredSupport
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.RequiredGuardSimple
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredGraph SourceEqualityNeeded
open SourceCurrentRequiredSupport
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentConstrainedCap (Cap)

private def annotation (guard : Bool) : Prop := guard = true
private def leafEdge := run (makeEdge (Symbol := Nat) 0 true []) empty
private def leafNode := run (makeNode [leafEdge.1]) leafEdge.2
private def openEdge := run (makeEdge 1 false [leafNode.1, .reference .depth]) leafNode.2
private def openNode := run (makeNode [openEdge.1]) openEdge.2
private def heap := openNode.2
private def value := openNode.1
private def needed : Needed := .node [(0, .node [])]

private theorem empty_semantic : SemanticReady (empty (Symbol := Nat) (Guard := Bool)) :=
  SourceEqualityRequiredSemanticCache.constructed .empty .empty empty (by simp only [InternedFreshOrdinaryConstruction.build])
private theorem leaf_edge :
    SourceEqualityRequiredCache.Keeps empty leafEdge.2 ∧
      InternedEdgeResidency.EdgeResident leafEdge.2 leafEdge.1 ∧ leafEdge.1.children = [] :=
  SourceEqualityRequiredCache.edge 0 true [] empty empty_semantic.ready (by intro _ member; cases member)
private theorem leaf_semantic : SemanticReady leafNode.2 :=
  (SourceEqualityOpenOrdinaryHead.node [leafEdge.1] leafEdge.2
    (SourceEqualityRequiredSemanticCache.edge 0 true [] empty empty_semantic (by intro _ member; cases member))
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ leaf_edge.2.1)).2.1
private theorem leaf_available : Available leafNode.2 leafNode.1 :=
  (SourceEqualityOpenOrdinaryHead.node [leafEdge.1] leafEdge.2
    (SourceEqualityRequiredSemanticCache.edge 0 true [] empty empty_semantic (by intro _ member; cases member))
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ leaf_edge.2.1)).2.2.1
private theorem open_inputs : Values leafNode.2 [leafNode.1, .reference .depth] := by
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact leaf_available
  · exact InternedNestedProvenance.depth_available _
private theorem open_edge : SourceEqualityRequiredCache.Keeps leafNode.2 openEdge.2 ∧
    InternedEdgeResidency.EdgeResident openEdge.2 openEdge.1 ∧
      openEdge.1.children = [leafNode.1, .reference .depth] :=
  SourceEqualityRequiredCache.edge 1 false _ leafNode.2 leaf_semantic.ready open_inputs
private theorem source_semantic : SemanticReady heap :=
  (SourceEqualityOpenOrdinaryHead.node [openEdge.1] openEdge.2
    (SourceEqualityRequiredSemanticCache.edge 1 false _ leafNode.2 leaf_semantic open_inputs)
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ open_edge.2.1)).2.1
private theorem source_available : Available heap value :=
  (SourceEqualityOpenOrdinaryHead.node [openEdge.1] openEdge.2
    (SourceEqualityRequiredSemanticCache.edge 1 false _ leafNode.2 leaf_semantic open_inputs)
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ open_edge.2.1)).2.2.1
private theorem source_costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  have first : InternedFreshOrdinaryCostHeap.Heap leafNode.2 :=
    InternedFreshOrdinaryCostHeap.preserve leafEdge.2 leafNode.2 InternedFreshOrdinaryCostHeap.empty_heap
      (InternedShallowHeap.makeNode_noNewMu [leafEdge.1] leafEdge.2)
  exact InternedFreshOrdinaryCostHeap.preserve openEdge.2 heap first
    (InternedShallowHeap.makeNode_noNewMu [openEdge.1] openEdge.2)
private theorem source_guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
  have first : SourceCurrentConstrainedCapGuardHeap.Heap annotation leafNode.2 :=
    SourceCurrentConstrainedCapGuardHeap.preserve annotation leafEdge.2 leafNode.2
      (SourceCurrentConstrainedCapGuardHeap.empty_heap annotation)
      (InternedShallowHeap.makeNode_noNewMu [leafEdge.1] leafEdge.2)
  exact SourceCurrentConstrainedCapGuardHeap.preserve annotation openEdge.2 heap first
    (InternedShallowHeap.makeNode_noNewMu [openEdge.1] openEdge.2)
private theorem leaf_shape : leafNode.1 = .node ⟨.node [0], 0⟩ [leafEdge.1] 0 [] := by cbv
private theorem source_shape : value = .node ⟨.node [1], 1⟩ [openEdge.1] 0 [.depth] := by cbv
private theorem leaf_annotated : Annotated annotation leafNode.1 := by
  rw [leaf_shape]
  apply Annotated.node
  · intro edge member
    have same : edge = leafEdge.1 := List.mem_singleton.mp member
    subst edge
    rfl
  · intro child member
    cases member
private theorem source_cap : Cap annotation 1 value := by
  rw [source_shape]
  apply Cap.node 0
  intro child member
  change child ∈ [leafNode.1, .reference .depth] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .plain 0 leaf_annotated
  · exact .plain 0 (.reference _)
private theorem source_open : value.free ≠ [] := by rw [source_shape]; decide
private theorem source_support : NodeSupport (fun _ => false) heap needed value := by
  intro path tip nonroot
  cases tip with
  | @child index entries child path found rest =>
      have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) _ _ found
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      have zero : index = 0 := Int.ofNat.inj member.1
      subst index
      refine Or.inr ⟨source_available, ?_⟩
      rw [source_shape]
      apply SourceCurrentSecondaryTrace.NodeTrace.branches (by decide)
      exact .next (.present rfl (.finite rfl)) .nil


end MicroCFTA.RequiredGuardSimple

namespace MicroCFTA.RequiredGuardIntegration
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

private def records := [selectedRecord, selectedRecord]
private theorem records_coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  have same : own = selectedRecord := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_coherent
private theorem records_active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = selectedRecord := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_active
private theorem records_domains : ∀ own ∈ records, ∀ path ∈ own.paths, Domain (path.map Int.ofNat) forest := by
  intro own member
  have same : own = selectedRecord := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_domains
private noncomputable def passCeiling :=
  SourceCurrentConstrainedCapClassForecast.foldProfile records forest.length parentProfile
private noncomputable def passFuel :=
  SourceCurrentConstrainedCapClassForecast.foldFuel records forest.length parentProfile


local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Context" => SourceCurrentAllocatedPartialInvariant.Context
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private theorem parent_probes : InternedFreshOrdinaryProbeHeap.Heap parentWork.2 := by
  have original : InternedFreshOrdinaryProbeHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryProbeHeap.closed_heap expression
  have edge := InternedFreshOrdinaryProbeHeap.edge ("parent", .top) parentGuard inputs heap original
  exact InternedFreshOrdinaryProbeHeap.node [parentEdge.1] parentEdge.2 edge

private theorem contradiction_ready (cache : Cache.State SourceEqualityPartialConstraintKey.Key) :
    SourceEqualityConstraintAllocation.Ready cache .contradiction := by
  refine ⟨True.intro, ?_⟩
  intro values impossible
  cases impossible

private def warmFourth := SourceCurrentEmptinessMemo.insert SourceCurrentEmptinessMemo.empty parent false
private theorem warmFourth_found : warmFourth parent.referenceOf = some (parent, false) := by
  simp [warmFourth, SourceCurrentEmptinessMemo.insert]
private theorem fourth_miss (width : Nat) :
    SourceCurrentConjunctionMemo.Call 0 SourceCurrentEmptinessMemo.empty parent
      (SourceCurrentAllocatedNativeEffects.physical (parentState width).checked) false
      (SourceCurrentAllocatedNativeEffects.physical (parentState width).checked) warmFourth :=
  .miss rfl (.open_input (by cbv))
private theorem fourth_correct (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentEmptinessMemo.Correct formulas solver parentWork.2 warmFourth := by
  have initial := parent_invariants width formulas solver
  exact (SourceCurrentConjunctionMemo.verified formulas solver (fourth_miss width)
    (SourceCurrentAllocatedConjunctionMemo.ready _ initial.1.ready.good initial.1.ready.semantic initial.1.ready.costs)
    initial.2.2.2.2.1 (SourceCurrentEmptinessMemo.empty_correct formulas solver parentWork.2)).2.1

private def baseCaller (width : Nat) : Caller width :=
  SourceCurrentAllocatedPartialState.initial (parentState width).checked SourceCurrentMemoMergeGraph.empty warmFourth
private def nodeRequest : SourceCurrentAllocatedPartialState.NodeRequest := ⟨.contradiction, parent⟩
private def edgeRequest : SourceCurrentAllocatedPartialState.EdgeRequest := ⟨.contradiction, parentEdge.1⟩
private def nodeCaller (width : Nat) : Caller width :=
  (SourceCurrentAllocatedPartialState.beginNode nodeRequest (baseCaller width)).2.2
private def edgeCaller (width : Nat) : Caller width :=
  (SourceCurrentAllocatedPartialState.beginEdge edgeRequest (nodeCaller width)).2.2
private def caller (width : Nat) : Caller width :=
  SourceCurrentAllocatedPartialState.finishEdge 0 parentEdge.1 (edgeCaller width)

private theorem node_running (width : Nat) :
    (caller width).nodeResults.cells 0 = some ⟨nodeRequest, .evaluating⟩ := by
  simp [caller, edgeCaller, nodeCaller, baseCaller, SourceCurrentAllocatedPartialState.finishEdge,
    SourceCurrentAllocatedPartialState.beginEdge, SourceCurrentAllocatedPartialState.beginNode,
    SourceCurrentAllocatedPartialState.initial, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]
private theorem edge_running (width : Nat) :
    (edgeCaller width).edgeResults.cells 0 = some ⟨edgeRequest, .evaluating⟩ := by
  simp [edgeCaller, nodeCaller, baseCaller, SourceCurrentAllocatedPartialState.beginEdge,
    SourceCurrentAllocatedPartialState.beginNode, SourceCurrentAllocatedPartialState.initial,
    FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]
private theorem edge_returned (width : Nat) :
    (caller width).edgeResults.cells 0 = some ⟨edgeRequest, .returned parentEdge.1⟩ :=
  SourceCurrentAllocatedPartialState.finishEdge_returned 0 edgeRequest parentEdge.1 (edgeCaller width) (edge_running width)

private theorem initial_context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  have initial := parent_invariants width formulas solver
  have base : Context formulas solver inventory (baseCaller width) EndpointMemoGateTrace.empty :=
    ⟨initial.1.ready, initial.1.admitted,
      SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver _ _ _,
      SourceCurrentMemoMergeEffects.stored_empty _, empty_covered formulas solver,
      fourth_correct width formulas solver, EndpointMemoGateTrace.empty_valid parentWork.2, parent_probes⟩
  have firstSound := SourceCurrentAllocatedPartialMemoSound.beginNode_sound formulas solver nodeRequest
    (baseCaller width) base.sound (contradiction_ready _) initial.2.2.2.2.1
  have first : Context formulas solver inventory (nodeCaller width) EndpointMemoGateTrace.empty :=
    base.rebase rfl rfl rfl firstSound
  have resident : InternedEdgeResidency.EdgeResident parentWork.2 parentEdge.1 := by
    have rows := InternedEdgeResidency.resident_edges parentWork.2 initial.1.ready.good.native.machine.1.linked
      parent initial.2.2.2.2.1.resident
    exact rows parentEdge.1 (by rw [parent_rows]; simp)
  have lastSound := SourceCurrentAllocatedPartialMemoSound.beginEdge_sound formulas solver edgeRequest
    (nodeCaller width) first.sound (contradiction_ready _) resident
  have last : Context formulas solver inventory (edgeCaller width) EndpointMemoGateTrace.empty :=
    first.rebase rfl rfl rfl lastSound
  have law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver edgeRequest parentEdge.1 := by
    intro ambient term
    exact ⟨id, fun _ => Iff.rfl⟩
  have finished := SourceCurrentAllocatedPartialMemoSound.finishEdge_sound formulas solver 0 edgeRequest
    parentEdge.1 (edgeCaller width) last.sound (edge_running width) resident law
  exact last.rebase rfl rfl rfl finished

private def selected : EqualityNormalize.Constraints := [selectedRecord.paths]
private def requiredPaths := SourceEqualitySelectedRequired.paths selected
private def requiredNeeded := SourceEqualityNeeded.build requiredPaths
private theorem selected_proper : ∀ path ∈ selected.flatten, path ≠ [] := by
  intro path retained
  change path ∈ selectedRecord.paths ++ [] at retained
  rw [selected_paths] at retained
  simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with rfl | rfl <;> decide
private theorem first_primary (unconstrained reaches : Value Symbol Guard → Bool) (state : State Symbol Guard) :
    EndpointStatefulGateTrace.NodeTrace unconstrained reaches [0] parent state false state := by
  apply EndpointStatefulGateTrace.NodeTrace.branches (by cbv)
  exact .next (.present (by cbv) (.finite (by cbv))) .nil
private theorem second_primary (unconstrained reaches : Value Symbol Guard → Bool) (state : State Symbol Guard) :
    EndpointStatefulGateTrace.NodeTrace unconstrained reaches [1] parent state false state := by
  apply EndpointStatefulGateTrace.NodeTrace.branches (by cbv)
  exact .next (.present (by cbv) (.finite (by cbv))) .nil
private theorem selected_primary (unconstrained reaches : Value Symbol Guard → Bool) (state : State Symbol Guard) :
    ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches forest paths state false state := by
  intro paths retained
  have same : paths = selectedRecord.paths := List.mem_singleton.mp retained
  subst paths
  rw [selected_paths]
  exact .next (.child (.present rfl (first_primary unconstrained reaches state)))
    (.next (.child (.present rfl (second_primary unconstrained reaches state))) .nil)

end MicroCFTA.RequiredGuardIntegration
