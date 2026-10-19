import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.SourceCurrentClassFoldRecursiveValueOrigins
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
# An actual native Mu is a new ordinary child

Two ordinary wrappers contain distinct source-built used Mu operands.
The literal class edits their child slots and returns a new used Mu below an ordinary inner row.
The exact new Mu does not occur in either original wrapper.
This fixture does not assert that the original gate is false.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.RecursiveValueAncestryKernels
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
private def wrapper (guard : Guard) : Syntax Symbol Guard :=
  .node [.mk ("wrapper",.top) top [recursive guard]]
private def expression : Syntax Symbol Guard := .node [.mk ("forest",.top) top [wrapper guardA,wrapper guardB]]
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
private def record := (SourceEqualityClassOrder.recordOf [[0,0],[1,0]]).getD ⟨.empty,[]⟩
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
    simp only [expression,wrapper,recursive,SourceEqualityConstraintOrigins.guards,
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
private noncomputable def parentRow := (nodeEdges result)[0]?.getD fallback
private noncomputable def innerValue := parentRow.children[0]?.getD .empty
private noncomputable def innerRow := (nodeEdges innerValue)[0]?.getD fallback
private noncomputable def needle := innerRow.children[0]?.getD .empty
private def oldA := (children first)[0]?.getD .empty
private def oldB := (children second)[0]?.getD .empty
private theorem class_done : classed = .done outputs classed.state classed.memo := by
  have tag : (match classed with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : classed with
  | done values state memo => simp only [outputs,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem shapes : outputs[0]? = some result ∧ (nodeEdges result)[0]? = some parentRow ∧
    parentRow.children[0]? = some innerValue ∧ parentRow.children = [innerValue] ∧
    parentRow.entry.key.symbol = ("wrapper",.top) ∧ parentRow.entry.key.constraint = top ∧
    (nodeEdges innerValue)[0]? = some innerRow ∧ innerRow.children[0]? = some needle ∧
    innerRow.entry.key.constraint = guardAB ∧ innerRow.children = [needle,needle,needle] ∧
    children first = [oldA] ∧ children second = [oldB] ∧
    (match needle with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧ nodeEdges needle = [] ∧
    (needle.referenceOf == oldA.referenceOf) = false ∧ (needle.referenceOf == oldB.referenceOf) = false := by
  exact ⟨by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv⟩
private theorem record_paths : record.paths = [[0,0],[1,0]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0],[1,0]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.terminal)]),(1,.branch [(0,.terminal)])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0,0],by simp,[1,0],by simp,by decide⟩
private theorem domains : ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs := by
  intro path member
  rw [record_paths] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionGraph.select,input_shape]
      using SourceCurrentRequiredEndpoints.closed_path [0] first heap (ready 0).semantic
        (available first (by rw [input_shape]; simp)) closed.1
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionGraph.select,input_shape]
      using SourceCurrentRequiredEndpoints.closed_path [0] second heap (ready 0).semantic
        (available second (by rw [input_shape]; simp)) closed.2
private theorem child_occurrence {value : Node} {rowIndex childIndex : Nat} {row child path needle}
    (selected : (nodeEdges value)[rowIndex]? = some row) (chosen : row.children[childIndex]? = some child)
    (rest : SourceCurrentClassRecursiveValueOrigins.Occurs child path needle) :
    SourceCurrentClassRecursiveValueOrigins.Occurs value (childIndex::path) needle := by
  cases value with
  | node entry edges depth free => exact .child rowIndex childIndex row child selected chosen rest
  | empty | reference | union | mu => simp only [nodeEdges,List.getElem?_nil] at selected; cases selected
private theorem recursive_occurrence {value : Node} {positions target}
    (recursive : SourceEqualityRequiredGraph.Recursive value)
    (actual : SourceCurrentClassRecursiveValueOrigins.Occurs value positions target) : target = value := by
  cases actual with
  | root => rfl
  | child => cases recursive
private theorem absent {original sourceChild : Node}
    (one : children original = [sourceChild]) (recursive : SourceEqualityRequiredGraph.Recursive sourceChild)
    (rootDifferent : (needle.referenceOf == original.referenceOf) = false)
    (childDifferent : (needle.referenceOf == sourceChild.referenceOf) = false) :
    ∀ positions, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs original positions needle := by
  intro positions actual
  cases actual with
  | root => simp at rootDifferent
  | @child entry edges depth free rowIndex childIndex row child selected chosen path target rest =>
    have member : child ∈ children (.node entry edges depth free) :=
      List.mem_flatMap.mpr ⟨row,List.mem_of_getElem? selected,List.mem_of_getElem? chosen⟩
    rw [one] at member
    have same : child = sourceChild := List.mem_singleton.mp member
    subst child
    have sameNeedle := recursive_occurrence recursive rest
    rw [sameNeedle] at childDifferent
    simp at childDifferent
private theorem occurrence : SourceCurrentClassRecursiveValueOrigins.Occurs result [0,0] needle := by
  rcases shapes with ⟨_,parent,chosen,_,_,_,inner,leaf,_,_,_,_,_,_,_,_⟩
  exact child_occurrence parent chosen (child_occurrence inner leaf (.root needle))
private theorem needle_recursive : SourceEqualityRequiredGraph.Recursive needle := by cbv
private theorem no_source : (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs first path needle) ∧
    (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs second path needle) := by
  rcases shapes with ⟨_,_,_,_,_,_,_,_,_,_,firstChildren,secondChildren,_,_,firstDifferent,secondDifferent⟩
  exact ⟨absent firstChildren (by cbv) (by cbv) firstDifferent,
    absent secondChildren (by cbv) (by cbv) secondDifferent⟩
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
private theorem node_event
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ (finish : SourceCurrentAllocatedSharedEditGraph.SharedState (bits+2)) (final : EndpointMemoGateTrace.Memos),
    ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditNode record inputs (.editBelow [(0,.editAt [0,0])]) first
        (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty) result finish,
      SourceCurrentAllocatedSharedEditGraph.NodeReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
      ∃ event suffix, SourceCurrentClassStructuralOrigins.Event formulas solver heap actual event ∧
        SourceCurrentClassRecursiveValueOrigins.Occurs event suffix needle := by
  obtain ⟨classFinal,classGraph,reads⟩ := class_reads formulas solver
  have found : ∀ entries, SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow entries →
      SourceEqualityNeededMap.lookup (0 : Int) entries = some (.editBelow [(0,.editAt [0,0])]) := by
    intro entries built
    have shape : SourceCurrentAllocatedClassEditPlan.compiled record =
        .editBelow [(0,.editBelow [(0,.editAt [0,0])]),(1,.editBelow [(0,.editAt [1,0])])] := by cbv
    have same := SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans shape)
    subst entries
    rfl
  obtain ⟨entries,shared,start,finish,current,returned,original,startInventory,_finishInventory,
      earlier,call,_later,_built,_sameState,_sameMemo,_output,input,_found,prefixRead,callRead,_suffixRead,
      safe,startReady,_finishReady,startHistory,_finishHistory,_first,_middle,_last,_readerGrowth⟩ :=
    SourceCurrentClassSelectedChildLineage.class_selected reads coherent active (ready (bits+2))
      (initial_frame formulas solver).admitted available domains (SourceCurrentMemoMergeEffects.stored_empty _)
      (empty_covered formulas solver) (EndpointMemoGateTrace.empty_valid _) (.initial machine operations) shapes.1 found
  have same : original = first := by
    simpa only [input_shape,List.getElem?_cons_zero,Option.some.injEq] using input.symm
  subst original
  cases earlier
  cases prefixRead
  have annotatedInput : Available heap first := available first (by rw [input_shape]; simp)
  have leaf : SourceCurrentEditDomains.HasLeaf (.editBelow [(0,.editAt ([0,0] : EqualityNormalize.Path))]) :=
    ⟨[0],[0,0],by simp [SourceEqualityEditLeafPaths.leaves]⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow [(0,.editAt [0,0])]) := by
    simp [SourceEqualitySharedEditEffects.Allowed,SourceEqualityEdits.All,record_paths]
  have populated : SourceCurrentEditDomains.Populated (.editBelow [(0,.editAt ([0,0] : EqualityNormalize.Path))]) := by
    simp [SourceCurrentEditDomains.Populated,SourceCurrentEditDomains.HasLeaf,SourceEqualityEditLeafPaths.leaves]
  have origin := SourceCurrentClassRecursiveValueOrigins.node callRead startInventory populated leaf allowed
    startReady annotatedInput safe (EndpointMemoGateTrace.empty_valid _) startHistory needle_recursive occurrence
  rcases origin with old | event
  · exact (no_source.1 _ old).elim
  · exact ⟨finish,returned,call,callRead,event⟩
private theorem fold_done : SourceCurrentAllocatedClassWorker.fold 4 8 8 64 16 256 records inputs
    (before (bits+2)) SourceCurrentMemoMergeGraph.empty = .done outputs classed.state classed.memo := by
  simpa only [records,SourceCurrentAllocatedClassWorker.fold,SourceCurrentAllocatedClassWorker.Outcome.bind,classed] using class_done
private theorem fold_event
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records inputs (before (bits+2))
        SourceCurrentMemoMergeGraph.empty outputs classed.state classed.memo,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      ∃ event residual, SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual 0 event ∧
        SourceCurrentClassRecursiveValueOrigins.Occurs event residual needle := by
  obtain ⟨final,classGraph,classReads⟩ := class_reads formulas solver
  have actual : SourceCurrentAllocatedClassPass.Fold records inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty outputs classed.state classed.memo := .cons .nil classGraph
  have reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual EndpointMemoGateTrace.empty final :=
    .cons .nil classReads
  have allCoherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
    intro own member
    have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false] using member
    exact same ▸ coherent
  have allActive : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
    intro own member
    have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false] using member
    exact same ▸ active
  have allDomains : ∀ own ∈ records, ∀ path ∈ own.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs := by
    intro own member
    have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false] using member
    exact same ▸ domains
  have origin := SourceCurrentClassFoldRecursiveValueOrigins.fold reads inventory allCoherent allActive
    (ready (bits+2)) (initial_frame formulas solver).admitted available allDomains
    (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
    (EndpointMemoGateTrace.empty_valid _) (.initial machine operations) 0 result shapes.1 needle_recursive occurrence
  rcases origin with ⟨original,present,sourceAt⟩ | event
  · have same : original = first := by
      simpa only [input_shape,List.getElem?_cons_zero,Option.some.injEq] using present.symm
    subst original
    exact (no_source.1 _ sourceAt).elim
  · exact ⟨final,actual,reads,event⟩
private theorem checked_witness
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ inputs = [first,second] ∧ record.paths = [[0,0],[1,0]] ∧ records = [record] ∧
    SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
    SourceCurrentConjunctionClassScan.Ready (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before (bits+2)) ∧
    SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling ∧ InternedNestedProvenance.Values heap inputs ∧
    classed = .done outputs classed.state classed.memo ∧
    SourceCurrentAllocatedClassWorker.fold 4 8 8 64 16 256 records inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty = .done outputs classed.state classed.memo ∧
    outputs[0]? = some result ∧ SourceCurrentClassRecursiveValueOrigins.Occurs result [0,0] needle ∧
    SourceEqualityRequiredGraph.Recursive needle ∧
    (match needle with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧ nodeEdges needle = [] ∧
    innerRow.entry.key.constraint = guardAB ∧ innerRow.children = [needle,needle,needle] ∧
    (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs first path needle) ∧
    (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs second path needle) ∧
    (∃ (finish : SourceCurrentAllocatedSharedEditGraph.SharedState (bits+2)) (final : EndpointMemoGateTrace.Memos),
      ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditNode record inputs (.editBelow [(0,.editAt [0,0])]) first
          (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty) result finish,
        SourceCurrentAllocatedSharedEditGraph.NodeReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        ∃ event suffix, SourceCurrentClassStructuralOrigins.Event formulas solver heap actual event ∧
          SourceCurrentClassRecursiveValueOrigins.Occurs event suffix needle) ∧
    (∃ final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records inputs (before (bits+2))
        SourceCurrentMemoMergeGraph.empty outputs classed.state classed.memo,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      ∃ event residual, SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual 0 event ∧
        SourceCurrentClassRecursiveValueOrigins.Occurs event residual needle) := by
  rcases shapes with ⟨selected,_,_,_,_,_,_,_,guard,children,_,_,used,noPhysicalRows,_,_⟩
  exact ⟨built_done,input_shape,record_paths,rfl,coherent,active,ready (bits+2),initial_frame formulas solver,
    initial_fits,width_room,available,class_done,fold_done,selected,occurrence,needle_recursive,
    used,noPhysicalRows,guard,children,no_source.1,no_source.2,node_event formulas solver,fold_event formulas solver⟩

/-- An exact new used Mu forces actual node-edit and class-fold event ancestry. -/
theorem recursive_events
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧ inputs = [first,second] ∧ record.paths = [[0,0],[1,0]] ∧ records = [record] ∧
    SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
    SourceCurrentConjunctionClassScan.Ready (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory (before (bits+2)) ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before (bits+2)) ∧
    SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling ∧ InternedNestedProvenance.Values heap inputs ∧
    classed = .done outputs classed.state classed.memo ∧
    SourceCurrentAllocatedClassWorker.fold 4 8 8 64 16 256 records inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty = .done outputs classed.state classed.memo ∧
    outputs[0]? = some result ∧ SourceCurrentClassRecursiveValueOrigins.Occurs result [0,0] needle ∧
    SourceEqualityRequiredGraph.Recursive needle ∧
    (match needle with
      | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
      | _ => False) ∧ nodeEdges needle = [] ∧
    innerRow.entry.key.constraint = guardAB ∧ innerRow.children = [needle,needle,needle] ∧
    (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs first path needle) ∧
    (∀ path, ¬ SourceCurrentClassRecursiveValueOrigins.Occurs second path needle) ∧
    (∃ (finish : SourceCurrentAllocatedSharedEditGraph.SharedState (bits+2)) (final : EndpointMemoGateTrace.Memos),
      ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditNode record inputs (.editBelow [(0,.editAt [0,0])]) first
          (SourceCurrentAllocatedSharedTargetState.initial (before (bits+2)) SourceCurrentMemoMergeGraph.empty) result finish,
        SourceCurrentAllocatedSharedEditGraph.NodeReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        ∃ event suffix, SourceCurrentClassStructuralOrigins.Event formulas solver heap actual event ∧
          SourceCurrentClassRecursiveValueOrigins.Occurs event suffix needle) ∧
    (∃ final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records inputs (before (bits+2))
        SourceCurrentMemoMergeGraph.empty outputs classed.state classed.memo,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      ∃ event residual, SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual 0 event ∧
        SourceCurrentClassRecursiveValueOrigins.Occurs event residual needle) := checked_witness formulas solver
end MicroCFTA.RecursiveValueAncestryKernels
