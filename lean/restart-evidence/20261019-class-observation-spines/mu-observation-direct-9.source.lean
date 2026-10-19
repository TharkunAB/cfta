import MicroCFTA.SourceCurrentClassObservationSpines
import MicroCFTA.SourceCurrentProjectionReadSpine
import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.SourceCurrentClassSelectedChildLineage
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentActualClassSemanticReads
import MicroCFTA.SourceCurrentParentInitialRoom
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentActualClassDispatch
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentAllocatedInheritedPrefix
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An actual native Mu result exposes a positive row

Two source-built used Mu operands have distinct positive body guards.
The original primary gate returns true. Required retains both Mu roots.
The literal class edit returns a Mu. A later row read unfolds it.
The observed row has the combined full guard. No productivity is claimed.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.MuObservationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := ⟨some [],.top⟩
private def guardA : Guard := ⟨some [[[0],[1]]],.top⟩
private def guardB : Guard := ⟨some [[[0],[2]]],.top⟩
private def guardAB : Guard := ⟨some [[[0],[1],[2]]],.top⟩
private def recursive (guard : Guard) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("inner",.top) guard [.var 0,.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("forest",.top) top [recursive guardA,recursive guardB]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def inputs := children root
private def first := inputs[0]?.getD .empty
private def second := inputs[1]?.getD .empty
private def one := SourceEqualityConstraintAllocation.construct guardA.equalities Cache.emptyState
private def oneValue : EqValue := match one.1 with | .ok value => value | .error _ => .contradiction
private def two := SourceEqualityConstraintAllocation.construct guardB.equalities one.2
private def twoValue : EqValue := match two.1 with | .ok value => value | .error _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct top.equalities two.2
private def inherited : EqValue := match allocation.1 with | .ok value => value | .error _ => .contradiction
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityConstraintMemoAllocation.initial allocation.2
private def before (width : Nat) : Checked width := ⟨initial width machine,operations⟩
private def record := (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def records := [record]
private theorem built_done : built = .done root heap := by cbv
private theorem input_shape : inputs = [first,second] := by cbv
private theorem cachedA : SourceEqualityGuardReadback.Cached guardA.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem cachedB : SourceEqualityGuardReadback.Cached guardB.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[2]]] = .normalized [[[0],[2]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem ready (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) := by
  have oneHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState one.2 [guardA] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cachedA (show one = (.ok oneValue,one.2) by cbv)
  have twoHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState two.2 [guardA,guardB] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      oneHistory cachedB (show two = (.ok twoValue,two.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [guardA,guardB,top] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      twoHistory SourceEqualityGuardReadback.empty_cached (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [guardA,guardB,top] := by
    intro guard member
    simp only [expression,recursive,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false] at member ⊢
    simpa only [or_assoc,or_left_comm,or_comm,or_self] using member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid
    expression covered root heap built_done).1
private theorem available : InternedNestedProvenance.Values heap inputs :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done).children
private theorem closed : first.free = [] ∧ second.free = [] := by constructor <;> cbv
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (ready 0).good.native.machine.1 first second
    (SourceRecursiveIntersectionOriginalOutput.closed_original first heap (ready 0).good.native.machine.1.coherent
      (available first (by rw [input_shape]; simp)) closed.1)
    (SourceRecursiveIntersectionOriginalOutput.closed_original second heap (ready 0).good.native.machine.1.coherent
      (available second (by rw [input_shape]; simp)) closed.2)
    (available first (by rw [input_shape]; simp)) (available second (by rw [input_shape]; simp)) closed.1 closed.2
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next,heap.edges.next,machine.domains.next,InternedValueMassHeap.initialBound heap⟩
private noncomputable def ceiling := SourceCurrentConstrainedCapClassForecast.foldProfile records inputs.length profile
private theorem exists_width : ∃ bits, 8 ≤ bits ∧ SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling := by
  let chosen := SourceCurrentParentInitialRoom.roomBits ceiling
  have room := SourceCurrentParentInitialRoom.room_computed ceiling
  refine ⟨chosen+8,by omega,?_⟩
  have pow0 : 2^chosen ≤ 2^(chosen+8) := Nat.pow_le_pow_right (by decide) (by omega)
  have pow1 : 2^(chosen+1) ≤ 2^(chosen+8+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have pow2 : 2^(chosen+2) ≤ 2^(chosen+8+2) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le room.1 pow0,Nat.le_trans room.2.1 pow2,Nat.lt_of_lt_of_le room.2.2 pow1⟩
private noncomputable opaque widthData : {n : Nat // 8 ≤ n ∧ SourceCurrentAllocatedNativeResourceForecast.Room n ceiling} :=
  ⟨Classical.choose exists_width,Classical.choose_spec exists_width⟩
private noncomputable def bits := widthData.val
private theorem width_large : 8 ≤ bits := widthData.property.1
private theorem width_room : SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling := widthData.property.2
private theorem wide : 1024 ≤ 2^(bits+2) := by
  change 2^10 ≤ 2^(bits+2)
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by have := width_large; omega)
private noncomputable def concreteWord (n : Nat) : BitVec (bits+2) :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h wide) else BitVec.ofNat (bits+2) n
private theorem word_small (n : Nat) : BitVec.ofNat (bits+2) n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^(bits+2) = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) wide)
  · rfl
attribute [local cbv_eval] word_small
private theorem symbolic_word : (BitVec.ofNat (bits+2) 5).toNat = 5 := by cbv
private noncomputable def classed := SourceCurrentAllocatedClassWorker.runClass 4 8 8 64 16 256
  record inputs (before (bits+2)) SourceCurrentMemoMergeGraph.empty
private noncomputable def outputs := match classed with | .done values .. => values | .failed .. => []
private noncomputable def result := outputs[0]?.getD .empty
private def fallback := (run (makeEdge ("missing",.top) top []) heap).1
private noncomputable def after := classed.state.native.machine.heap
private noncomputable def projected := SourceEqualityProjectionWorker.forest 2 0 [0] outputs after
private noncomputable def unfoldCall := InternedFreshOrdinaryStoredSubstitution.unfold result after
private noncomputable def exposed : Node := match unfoldCall with | .done value _ => value | _ => .empty
private noncomputable def unfoldedHeap := unfoldCall.state
private noncomputable def readCall := MergedFreshOrdinaryExposure.nodeEdges 4 result after
private noncomputable def observed := match readCall with | .done rows _ => rows | _ => []
private noncomputable def reader := readCall.state
private noncomputable def row := observed[0]?.getD fallback
private theorem class_done : classed = .done outputs classed.state classed.memo := by
  have tag : (match classed with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : classed with
  | done values state memo => simp only [outputs,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem original_gate : SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths (before (bits+2)) =
    .done true (before (bits+2)) := by cbv
private theorem required_identity : SourceEqualityRequiredExecution.requireAll 4 0
    (record.paths.map (List.map Int.ofNat)) inputs heap = .done inputs heap := by cbv
private theorem selected : outputs[0]? = some result := by cbv
private theorem mu_result : (match result with
  | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
  | _ => False) := by cbv
private theorem projected_done : projected = .done result after := by cbv
private theorem unfolded_done : unfoldCall = .done exposed unfoldedHeap := by cbv
private theorem read_done : readCall = .done observed reader := by cbv
private theorem observed_facts : observed[0]? = some row ∧ row.entry.key.constraint = guardAB ∧
    row.entry.key.symbol = ("inner",.top) ∧ row.children = [result,result,result] ∧ nodeEdges result = [] := by
  exact ⟨by cbv,by cbv,by cbv,by cbv,by cbv⟩
private noncomputable def descendantCall := SourceEqualityProjectionWorker.project 4 4 [0] result after
private noncomputable def descendant : Node := match descendantCall with | .done value _ => value | _ => .empty
private noncomputable def descendantHeap := match descendantCall with
  | .done _ state | .pending _ state | .unresolved _ state | .exhausted _ state => state
private noncomputable def terminalRead := MergedFreshOrdinaryExposure.nodeEdges 4 descendant descendantHeap
private noncomputable def terminalRows := match terminalRead with | .done rows _ => rows | _ => []
private noncomputable def terminalHeap := terminalRead.state
private noncomputable def terminalRow := terminalRows[0]?.getD fallback
private theorem descendant_done : descendantCall = .done descendant descendantHeap := by cbv
private theorem forest_descendant_done : SourceEqualityProjectionWorker.forest 4 4 [0,0] outputs after =
    .done descendant descendantHeap := by cbv
private theorem terminal_done : terminalRead = .done terminalRows terminalHeap := by cbv
private theorem descendant_facts : terminalRows[0]? = some terminalRow ∧
    terminalRow.entry.key.constraint = guardAB ∧ terminalRow.entry.key.symbol = ("inner",.top) ∧
    terminalRow.children = [result,result,result] ∧ nodeEdges result = [] ∧
    (match descendant with | .node .. => True | _ => False) := by
  exact ⟨by cbv,by cbv,by cbv,by cbv,by cbv,by cbv⟩
private theorem projectionGraph : SourceEqualityProjectionGraph.Project [0] result after descendant descendantHeap :=
  SourceEqualityProjectionWorkerSound.project_graph 4 4 [0] result after descendant descendantHeap descendant_done
private theorem terminalGraph : SourceEqualityProjectionRead.Read descendant descendantHeap terminalRows terminalHeap :=
  .done 4 terminal_done
private theorem record_paths : record.paths = [[0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.terminal),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0],by simp,[1],by simp,by decide⟩
private theorem domains : ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs := by
  intro path member
  rw [record_paths] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select,input_shape] using closed.1
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select,input_shape] using closed.2
private theorem initial_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain expression
private theorem initial_frame
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory (before (bits+2)) :=
  SourceCurrentConstrainedCapGeneratedQueryResources.Frame.initial formulas solver inventory machine operations
    (ready (bits+2)) initial_guards rfl
private theorem initial_fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before (bits+2)) :=
  ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,InternedValueMassHeap.initial heap (ready (bits+2)).good.native.machine.1⟩
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : Memo) := by
  intro ambient key entry absent
  cases absent
private theorem class_room : SourceCurrentAllocatedNativeResourceForecast.Room bits
    (SourceCurrentConstrainedCapClassForecast.classProfile record inputs.length profile) := by
  simpa only [ceiling,records,SourceCurrentConstrainedCapClassForecast.foldProfile] using width_room
private theorem class_support
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceEqualityRequiredSemanticCache.SemanticReady after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧
      Available after result := by
  obtain ⟨_next,_final,_actual,_reads,receipt,_frame,_fits,_length⟩ :=
    SourceCurrentActualClassSemanticReads.class_reads formulas solver inventory record coherent active inputs
      (before (bits+2)) SourceCurrentMemoMergeGraph.empty profile (initial_frame formulas solver) initial_fits available
      domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) class_room class_done
  exact ⟨receipt.ready.semantic,receipt.ready.costs,receipt.available result (List.mem_of_getElem? selected)⟩
private theorem spine
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentProjectionReadSpine.Spine projectionGraph terminalGraph 0 terminalRow := by
  obtain ⟨semantic,costs,resident⟩ := class_support formulas solver
  exact SourceCurrentProjectionReadSpine.project projectionGraph semantic costs resident terminalGraph 0 terminalRow
    descendant_facts.1
private theorem class_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ final, ∃ actual : SourceCurrentAllocatedClassEdits.Class record inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty outputs classed.state classed.memo,
      SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual EndpointMemoGateTrace.empty final := by
  obtain ⟨_next,final,actual,reads,_receipt,_frame,_fits,_length⟩ :=
    SourceCurrentActualClassSemanticReads.class_reads formulas solver inventory record coherent active inputs
      (before (bits+2)) SourceCurrentMemoMergeGraph.empty profile (initial_frame formulas solver) initial_fits available
      domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) class_room class_done
  exact ⟨final,actual,reads⟩
private theorem leaf_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ next finish final, SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record inputs heap [0]
      first (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty)
      result finish EndpointMemoGateTrace.empty final ∧
      SourceEqualityRequiredCache.Keeps finish.checked.native.machine.heap after := by
  obtain ⟨classFinal,classGraph,reads⟩ := class_reads formulas solver
  have found : ∀ entries, SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow entries →
      SourceEqualityNeededMap.lookup (0 : Int) entries = some (.editAt [0]) := by
    intro entries built
    have shape : SourceCurrentAllocatedClassEditPlan.compiled record =
        .editBelow [(0,.editAt [0]),(1,.editAt [1])] := by cbv
    have same := SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans shape)
    subst entries
    rfl
  obtain ⟨entries,shared,start,finish,current,returned,original,startInventory,_finishInventory,
      earlier,call,_later,_built,_sameState,_sameMemo,_output,input,_found,prefixRead,callRead,_suffixRead,
      _safe,_startReady,_finishReady,_startHistory,_finishHistory,_first,_middle,_last,_readerGrowth⟩ :=
    SourceCurrentClassSelectedChildLineage.class_selected reads coherent active (ready (bits+2))
      (initial_frame formulas solver).admitted available domains (SourceCurrentMemoMergeEffects.stored_empty _)
      (empty_covered formulas solver) (EndpointMemoGateTrace.empty_valid _) (.initial machine operations) selected found
  have same : original = first := by
    simpa only [input_shape,List.getElem?_cons_zero,Option.some.injEq] using input.symm
  subst original
  cases earlier
  cases prefixRead
  cases callRead with
  | leaf receipt =>
      have fullSafe := SourceCurrentAllocatedClassEditPlan.compiled_safe record coherent inputs domains entries _built
      have suffixSafe : SourceCurrentEditDomains.ChildrenSafe entries (0+0+1) (inputs.drop (0+1)) := by
        intro query child found value present
        apply fullSafe (query+1) child
        · simpa only [Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using found
        · simpa only [List.getElem?_drop,Nat.add_comm] using present
      have populated : SourceCurrentEditDomains.Populated (.editBelow entries) := by
        rw [← _built]
        exact SourceCurrentAllocatedClassEditPlan.compiled_populated record
      have allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow entries) := by
        rw [← _built]
        exact SourceCurrentAllocatedClassEditPlan.compiled_allowed record
      have remaining : InternedNestedProvenance.Values finish.checked.native.machine.heap (inputs.drop (0+1)) := by
        intro value member
        exact _finishReady.captured.available value (available value (List.mem_of_mem_drop member))
      obtain ⟨_next,suffix⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects _suffixRead
        populated allowed _finishReady remaining suffixSafe receipt.globals.valid
      refine ⟨_,_,_,receipt,?_⟩
      simpa only [after,_sameState,SourceCurrentAllocatedNativeEffects.physical] using suffix.effects.keeps
private theorem head_warm_schedule :
    SourceEqualityRequiredWorker.head 4 result after = .done descendant unfoldedHeap ∧
    descendantHeap = unfoldedHeap ∧ descendant = exposed ∧ terminalRow = row ∧
    MergedFreshOrdinaryExposure.nodeEdges 4 result unfoldedHeap = .done observed unfoldedHeap := by
  exact ⟨by cbv,by cbv,by cbv,by cbv,by cbv⟩
private theorem checked_witness
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ inputs = [first,second] ∧ first ≠ second ∧
    (match first with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    (match second with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
    8 ≤ bits ∧ SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling ∧
    SourceCurrentConjunctionClassScan.Ready (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before (bits+2)) ∧
    InternedNestedProvenance.Values heap inputs ∧
    SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths (before (bits+2)) = .done true (before (bits+2)) ∧
    SourceEqualityRequiredExecution.requireAll 4 0 (record.paths.map (List.map Int.ofNat)) inputs heap = .done inputs heap ∧
    classed = .done outputs classed.state classed.memo ∧ outputs[0]? = some result ∧
    (match result with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    nodeEdges result = [] ∧
    unfoldCall = .done exposed unfoldedHeap ∧ readCall = .done observed reader ∧
    observed[0]? = some row ∧ row.entry.key.constraint = guardAB ∧ row.children = [result,result,result] ∧
    descendantCall = .done descendant descendantHeap ∧
    SourceEqualityProjectionWorker.forest 4 4 [0,0] outputs after = .done descendant descendantHeap ∧
    terminalRead = .done terminalRows terminalHeap ∧ terminalRows[0]? = some terminalRow ∧
    terminalRow.entry.key.symbol = ("inner",.top) ∧ terminalRow.entry.key.constraint = guardAB ∧
    SourceMemoGate.plain terminalRow.entry.key.constraint = false ∧
    terminalRow.children = [result,result,result] ∧
    (match descendant with | .node .. => True | _ => False) ∧
    SourceEqualityRequiredWorker.head 4 result after = .done descendant unfoldedHeap ∧
    descendantHeap = unfoldedHeap ∧ descendant = exposed ∧ terminalRow = row ∧
    MergedFreshOrdinaryExposure.nodeEdges 4 result unfoldedHeap = .done observed unfoldedHeap ∧
    SourceCurrentProjectionReadSpine.Spine projectionGraph terminalGraph 0 terminalRow ∧
    (∃ next finish final,
      ∃ receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record inputs heap [0] first
        (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty)
        result finish EndpointMemoGateTrace.empty final,
      SourceEqualityRequiredCache.Keeps finish.checked.native.machine.heap after ∧
      SourceCurrentClassObservationSpines.Spine formulas solver heap (.leaf receipt.actual)
        projectionGraph terminalGraph 0 terminalRow true) := by
  have sourceUsed : (match first with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧ (match second with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) := by exact ⟨by cbv,by cbv⟩
  have distinct : first ≠ second := by
    have different : (first.referenceOf == second.referenceOf) = false := by cbv
    intro same
    rw [same] at different
    simp at different
  have leaf : ∃ next finish final,
      ∃ receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record inputs heap [0] first
        (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty)
        result finish EndpointMemoGateTrace.empty final,
      SourceEqualityRequiredCache.Keeps finish.checked.native.machine.heap after ∧
      SourceCurrentClassObservationSpines.Spine formulas solver heap (.leaf receipt.actual)
        projectionGraph terminalGraph 0 terminalRow true := by
    obtain ⟨next,finish,final,receipt,keeps⟩ := leaf_receipt formulas solver
    exact ⟨next,finish,final,receipt,keeps,
      .leaf receipt.reads (.initial machine operations) (spine formulas solver)⟩
  exact ⟨built_done,input_shape,distinct,sourceUsed.1,sourceUsed.2,record_paths,coherent,active,
    width_large,width_room,ready (bits+2),initial_frame formulas solver,initial_fits,available,
    original_gate,required_identity,class_done,selected,mu_result,observed_facts.2.2.2.2,
    unfolded_done,read_done,observed_facts.1,observed_facts.2.1,observed_facts.2.2.2.1,
    descendant_done,forest_descendant_done,terminal_done,descendant_facts.1,descendant_facts.2.2.1,
    descendant_facts.2.1,by cbv,descendant_facts.2.2.2.1,descendant_facts.2.2.2.2.2,
    head_warm_schedule.1,head_warm_schedule.2.1,head_warm_schedule.2.2.1,head_warm_schedule.2.2.2.1,
    head_warm_schedule.2.2.2.2,spine formulas solver,leaf⟩

/-- An actual native Mu class result retains its recursive projection and selected row-read continuation. -/
theorem native_mu_spine
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ inputs = [first,second] ∧ first ≠ second ∧
    (match first with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    (match second with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
    8 ≤ bits ∧ SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling ∧
    SourceCurrentConjunctionClassScan.Ready (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before (bits+2)) ∧
    InternedNestedProvenance.Values heap inputs ∧
    SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths (before (bits+2)) = .done true (before (bits+2)) ∧
    SourceEqualityRequiredExecution.requireAll 4 0 (record.paths.map (List.map Int.ofNat)) inputs heap = .done inputs heap ∧
    classed = .done outputs classed.state classed.memo ∧ outputs[0]? = some result ∧
    (match result with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧
    nodeEdges result = [] ∧
    unfoldCall = .done exposed unfoldedHeap ∧ readCall = .done observed reader ∧
    observed[0]? = some row ∧ row.entry.key.constraint = guardAB ∧ row.children = [result,result,result] ∧
    descendantCall = .done descendant descendantHeap ∧
    SourceEqualityProjectionWorker.forest 4 4 [0,0] outputs after = .done descendant descendantHeap ∧
    terminalRead = .done terminalRows terminalHeap ∧ terminalRows[0]? = some terminalRow ∧
    terminalRow.entry.key.symbol = ("inner",.top) ∧ terminalRow.entry.key.constraint = guardAB ∧
    SourceMemoGate.plain terminalRow.entry.key.constraint = false ∧
    terminalRow.children = [result,result,result] ∧
    (match descendant with | .node .. => True | _ => False) ∧
    SourceEqualityRequiredWorker.head 4 result after = .done descendant unfoldedHeap ∧
    descendantHeap = unfoldedHeap ∧ descendant = exposed ∧ terminalRow = row ∧
    MergedFreshOrdinaryExposure.nodeEdges 4 result unfoldedHeap = .done observed unfoldedHeap ∧
    SourceCurrentProjectionReadSpine.Spine projectionGraph terminalGraph 0 terminalRow ∧
    (∃ next finish final,
      ∃ receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record inputs heap [0] first
        (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty)
        result finish EndpointMemoGateTrace.empty final,
      SourceEqualityRequiredCache.Keeps finish.checked.native.machine.heap after ∧
      SourceCurrentClassObservationSpines.Spine formulas solver heap (.leaf receipt.actual)
        projectionGraph terminalGraph 0 terminalRow true) := checked_witness formulas solver
end MicroCFTA.MuObservationKernels
