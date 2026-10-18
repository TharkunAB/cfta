import MicroCFTA.SourceCurrentFiniteEditGuardAlphabet
import MicroCFTA.SourceCurrentEditGuardScans
import MicroCFTA.SourceCurrentConjunctionGuardUniverse
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

noncomputable section

namespace MicroCFTA.EditScanKernels
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
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
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
private theorem initially_missing (width : Nat) : (start width).targets [0] = none := rfl

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

open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
private def alphabet := SourceCurrentConjunctionGuardUniverse.guards heap
private def entries : List (Int × Edits EqualityNormalize.Path) := [(0, .editAt [0])]
private def pairs : List (Path × EqualityNormalize.Path) := [([0], [0])]
private theorem compiled : build pairs = .editBelow entries := by cbv
private def level := sizeOf (Edits.editAt [0] : Edits EqualityNormalize.Path)
private def ceiling := SourceCurrentConstrainedCapEditForecast.scan
  (SourceCurrentConstrainedCapEditForecast.planProfile record inputs.length level) inputs.length profile
private def steps := SourceCurrentEditGuardBudget.nodeBound record inputs.length ceiling level
private def sharedFuel := SourceCurrentConstrainedCapEditForecast.stageFuel record inputs.length ceiling
private def childWorker {width : Nat} (before : Shared width) := SourceCurrentAllocatedSharedEditWorker.children
  (SourceCurrentAllocatedSharedEditWorker.edit record inputs (SourceCurrentEditGuardScans.editFuel level)
    sharedFuel sharedFuel sharedFuel sharedFuel sharedFuel) entries 0 inputs before

private theorem sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
  intro index child member
  simp only [entries,List.mem_singleton,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩
  exact Nat.le_refl _
private theorem populated : Populated (.editBelow entries) := by
  rw [← compiled]
  exact build_populated pairs
private theorem allowed : Allowed record (.editBelow entries) := by
  rw [← compiled]
  apply build_all (fun path => path ∈ record.paths) pairs
  intro path target included
  simp only [pairs,List.mem_singleton,Prod.mk.injEq] at included
  rcases included with ⟨rfl,rfl⟩
  exact member
private theorem safe : ChildrenSafe entries 0 inputs := by
  intro query child found value selected
  have mem := SourceEqualityNeededMap.lookup_mem _ _ _ found
  simp only [entries,List.mem_singleton,Prod.mk.injEq] at mem
  have keyZero : (query : Int) = 0 := by simpa only [Nat.zero_add,Int.ofNat_eq_natCast] using mem.1
  have zero : query = 0 := by omega
  subst query
  have edits : child = .editAt [0] := mem.2
  subst child
  have same : left = value := by simpa only [inputs,List.getElem?_cons_zero,Option.some.injEq] using selected
  subst value
  exact closed_safe (.editAt [0]) left heap initial_semantic originals.1 initial_closed.1

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
    SourceEqualityNeededMap.lookup 0 entries = some (.editAt [0]) ∧
    SourceEqualityNeededMap.lookup 1 entries = none ∧
    ∃ bits results after next final,
      ∃ actual : EditChildren record inputs entries 0 inputs (start (bits+2)) results after,
        ChildrenReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record inputs heap inputs
          (start (bits+2)) results after EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after.checked ∧ QueryFits ceiling after.checked ∧
        SourceEqualityAnnotationHeap.Heap
          (fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.advance alphabet (inputs.length * steps))
          after.checked.native.machine.heap ∧
        childWorker (start (bits+2)) = .done results after := by
  obtain ⟨bits,room⟩ := exists_room ceiling
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready (bits+2)) initial_guards rfl
  have known := SourceCurrentConjunctionGuardUniverse.initial heap (initial_good (bits+2)).native.machine.1
  have node := SourceCurrentFiniteEditGuardAlphabet.node_complete (bits := bits) level ceiling formulas solver record inputs heap
    (input_available (bits+2)) domains record_coherent record_active
  obtain ⟨results,after,next,final,actual,reads,receipt,returned,fits,carrier,done⟩ :=
    SourceCurrentEditGuardScans.children formulas solver record inputs heap level alphabet ceiling node
      entries sizes 0 inputs (start (bits+2)) inventory profile populated allowed
      (start_ready (bits+2) formulas solver) frame (initial_fits (bits+2)) (input_available (bits+2)) safe
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
      (SourceCurrentAllocatedNativeResourceForecast.Le.refl _) room known
  exact ⟨constructed,open_input,by cbv,by cbv,bits,results,after,next,final,actual,reads,receipt,returned,fits,carrier,done⟩

/-- The actual compiler selects one closed Leaf and leaves the other ordinary and open siblings unselected. -/
theorem selected_and_unselected (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
    SourceEqualityNeededMap.lookup 0 entries = some (.editAt [0]) ∧
    SourceEqualityNeededMap.lookup 1 entries = none ∧
    ∃ bits results after next final,
      ∃ actual : EditChildren record inputs entries 0 inputs (start (bits+2)) results after,
        ChildrenReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record inputs heap inputs
          (start (bits+2)) results after EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after.checked ∧ QueryFits ceiling after.checked ∧
        SourceEqualityAnnotationHeap.Heap
          (fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.advance alphabet (inputs.length * steps))
          after.checked.native.machine.heap ∧
        childWorker (start (bits+2)) = .done results after := witness formulas solver

end MicroCFTA.EditScanKernels

#check @MicroCFTA.EditScanKernels.selected_and_unselected
#print MicroCFTA.EditScanKernels.selected_and_unselected
#print axioms MicroCFTA.EditScanKernels.selected_and_unselected
