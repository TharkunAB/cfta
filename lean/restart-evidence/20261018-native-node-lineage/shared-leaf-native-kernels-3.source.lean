import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceCurrentLeafNumeric
import MicroCFTA.SourceCurrentSharedEditChildLineage
import MicroCFTA.SourceCurrentEditListNumeric
import MicroCFTA.SourceCurrentSharedEditRowLineage
import MicroCFTA.SourceCurrentParentRowWriterLineage
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

namespace MicroCFTA.SharedLeafNativeIntegration
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

local notation "History" => SourceCurrentNativeEdgeWriterGrowth.History
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "SlotReceipt" => SourceCurrentAllocatedSharedTargetState.SlotReceipt
private def operands := SourceEqualityClassTarget.operandPaths record.paths [0]
private def firstProfile := SourceCurrentConstrainedCapSharedForecast.leafProfile inputs.length operands false profile
private def finalProfile := SourceCurrentConstrainedCapSharedForecast.leafProfile inputs.length operands true firstProfile
private theorem reserved_from_room (bits : Nat)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits firstProfile) :
    SourceCurrentConstrainedCapSharedForecast.LeafReserved bits inputs.length operands false profile := by
  have forceRoom := room.mono (SourceCurrentConstrainedCapSharedForecast.forceProfile_le_leafProfile inputs.length operands false profile)
  refine ⟨?_,forceRoom⟩
  change SourceCurrentConstrainedCapTargetForecast.TargetReserved bits inputs.length operands profile
  have shape : operands = [[1]] := by cbv
  rw [shape]
  trivial
private theorem present_of_leaf {bits : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {next value memos final} {before after : Shared (bits + 2)}
    (receipt : LeafReceipt formulas solver next record inputs heap [0] left before value after memos final) :
    ∃ target, after.targets [0] = some target := by
  cases receipt.reads with
  | apply forced query => exact ⟨_,forced.present⟩

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits first second middle after current final firstInventory secondInventory,
      LeafReceipt formulas solver firstInventory record inputs heap [0] left
        (start (bits + 2)) first middle EndpointMemoGateTrace.empty current ∧
      LeafReceipt formulas solver secondInventory record inputs heap [0] left middle second after current final ∧
      ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      History middle.checked ∧ History after.checked ∧
      ∃ target, middle.targets [0] = some target ∧
        SlotReceipt (bits + 2) formulas solver record inputs middle.checked.native.machine.heap middle.memo [0] target ∧
        ∃ fuel, Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain target left))
          middle.checked (.code (.pure second)) after.checked ∧
        ∃ handle, after.checked.native.nodes.cells handle =
            some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,left⟩,.returned second⟩ ∧
          SourceCurrentNativeWriterReadyRetention.Written (width := bits + 2) handle
            ⟨IntersectionEmptyDomain.emptyDomain,target,left⟩ second after.checked.native := by
  obtain ⟨bits,room⟩ := exists_room finalProfile
  have firstRoom := room.mono (SourceCurrentConstrainedCapSharedForecast.leafProfile_ge inputs.length operands true firstProfile)
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready (bits + 2)) initial_guards rfl
  obtain ⟨first,middle,firstInventory,current,firstReceipt,firstFrame,firstFits,_firstDone⟩ :=
    SourceCurrentLeafNumeric.complete formulas solver inventory record inputs heap (start (bits + 2)) profile
      (start_ready (bits + 2) formulas solver) frame (initial_fits (bits + 2)) (input_available (bits + 2))
      domains record_coherent record_active [0] member left originals.1 initial_closed.1
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) (reserved_from_room bits firstRoom)
  have beforeHistory : History (start (bits + 2)).checked := .initial machine operations
  have firstHistory := SourceCurrentParentNativeHistory.leaf firstReceipt beforeHistory
  obtain ⟨target,present⟩ := present_of_leaf firstReceipt
  have secondReserved : SourceCurrentConstrainedCapSharedForecast.LeafReserved bits inputs.length operands (middle.targets [0]).isSome firstProfile := by
    rw [present]
    exact ⟨trivial,firstRoom⟩
  obtain ⟨second,after,secondInventory,final,secondReceipt,_secondFrame,_secondFits,_secondDone⟩ :=
    SourceCurrentLeafNumeric.complete formulas solver firstInventory record inputs heap middle firstProfile
      firstReceipt.ready firstFrame firstFits (input_available (bits + 2)) domains record_coherent record_active [0] member
      left (firstReceipt.effects.keeps.available left originals.1) initial_closed.1
      current firstReceipt.globals.valid secondReserved
  obtain ⟨chosen,forced,forceInventory,next,capturedBase,forceReceipt,query,afterShape,slot,
    forceHistory,afterHistory,_forceGood,_afterGood,_beforeGrowth,_queryGrowth,origin⟩ :=
      SourceCurrentSharedLeafNativeLineage.leaf secondReceipt.reads firstHistory
  cases forceReceipt.actual with
  | hit found =>
    have same : chosen = target := Option.some.inj (found.symm.trans present)
    subst chosen
    obtain ⟨handle,cell,writer⟩ := origin.returned forceReceipt.closed initial_closed.1
    cases query.actual with
    | run trace =>
      exact ⟨bits,first,second,middle,after,current,final,firstInventory,secondInventory,
        firstReceipt,secondReceipt,open_input,firstHistory,afterHistory,target,present,slot,_,trace,handle,cell,writer⟩
  | miss absent targetCall =>
    rw [present] at absent
    cases absent

/-- Own initial reservations construct a missing force, then a same-path slot hit and its exact native writer. -/
theorem missing_then_hit (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits first second middle after current final firstInventory secondInventory,
      LeafReceipt formulas solver firstInventory record inputs heap [0] left
        (start (bits + 2)) first middle EndpointMemoGateTrace.empty current ∧
      LeafReceipt formulas solver secondInventory record inputs heap [0] left middle second after current final ∧
      ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      History middle.checked ∧ History after.checked ∧
      ∃ target, middle.targets [0] = some target ∧
        SlotReceipt (bits + 2) formulas solver record inputs middle.checked.native.machine.heap middle.memo [0] target ∧
        ∃ fuel, Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain target left))
          middle.checked (.code (.pure second)) after.checked ∧
        ∃ handle, after.checked.native.nodes.cells handle =
            some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,left⟩,.returned second⟩ ∧
          SourceCurrentNativeWriterReadyRetention.Written (width := bits + 2) handle
            ⟨IntersectionEmptyDomain.emptyDomain,target,left⟩ second after.checked.native := witness formulas solver

private theorem direct_call : Trace 1
    (.code (requestNode IntersectionEmptyDomain.emptyDomain (.reference .depth) (.empty : Value Symbol Guard)))
    (before 8) (.code (.pure .empty)) (before 8) := by
  refine Trace.cons _ _ _ _ _ _ _ ?_ ?_ (.refl _ _)
  · refine ⟨⟨empty_domain _,InternedNestedProvenance.depth_available _,InternedNestedProvenance.empty_available _⟩,?_⟩
    intro key found
    cbv at found
    cases found
  · cbv
private theorem direct_witness :
    History (before 8) ∧ Good (before 8) ∧
    SourceCurrentSharedLeafNativeLineage.Origin
      ⟨IntersectionEmptyDomain.emptyDomain,.reference .depth,.empty⟩ (before 8) .empty (before 8) ∧
    (∀ handle, (before 8).native.nodes.cells handle = none) := by
  have checked := SourceCurrentSharedLeafNativeLineage.request
    ⟨IntersectionEmptyDomain.emptyDomain,.reference .depth,.empty⟩ 1 .empty (initial_good 8)
    (.initial machine operations) direct_call
  exact ⟨checked.1,checked.2.1,checked.2.2.2,by intro handle; rfl⟩

/-- An actual unresolved reference request takes the direct empty shortcut without a memo cell. -/
theorem unresolved_empty_shortcut :
    History (before 8) ∧ Good (before 8) ∧
    SourceCurrentSharedLeafNativeLineage.Origin
      ⟨IntersectionEmptyDomain.emptyDomain,.reference .depth,.empty⟩ (before 8) .empty (before 8) ∧
    (∀ handle, (before 8).native.nodes.cells handle = none) := direct_witness
end MicroCFTA.SharedLeafNativeIntegration
