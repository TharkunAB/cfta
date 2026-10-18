import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
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
# A descendant guard requires an actual class event

Two source-built wrappers contain distinct positive inner guards.
The actual class query combines these guards at a descendant row.
The original selected input has no row with the combined full guard.
Two repeated coherent active records form a literal right-fold schedule.
This schedule is not claimed to be a unique record-scan output.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ClassFoldStructuralKernels
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
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def inner (guard : Guard) : Syntax Symbol Guard := .node [.mk ("inner",.top) guard [leaf,leaf,leaf]]
private def wrapper (guard : Guard) : Syntax Symbol Guard := .node [.mk ("wrapper",.top) top [inner guard]]
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
private def record := (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def records := [record,record]
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
    simp only [expression,wrapper,inner,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member ⊢
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
private noncomputable def classValues := match classed with | .done values .. => values | .failed .. => []
private noncomputable def called := SourceCurrentAllocatedClassWorker.fold 4 8 8 64 16 256
  records inputs (before (bits+2)) SourceCurrentMemoMergeGraph.empty
private noncomputable def outputs := match called with | .done values .. => values | .failed .. => []
private noncomputable def result := outputs[0]?.getD .empty
private noncomputable def classResult := classValues[0]?.getD .empty
private def fallback := (run (makeEdge ("missing",.top) top []) heap).1
private noncomputable def parentRow := (nodeEdges result)[0]?.getD fallback
private noncomputable def child := parentRow.children[0]?.getD .empty
private noncomputable def row := (nodeEdges child)[0]?.getD fallback
private theorem class_done : classed = .done classValues classed.state classed.memo := by
  have tag : (match classed with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : classed with
  | done values state memo => simp only [classValues,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem called_done : called = .done outputs called.state called.memo := by
  have tag : (match called with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : called with
  | done values state memo => simp only [outputs,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem output_facts : outputs[0]? = some result ∧ classValues[0]? = some classResult ∧
    classResult = result ∧ (nodeEdges result)[0]? = some parentRow ∧ parentRow.children[0]? = some child ∧
    (nodeEdges child)[0]? = some row ∧ row.entry.key.constraint = guardAB := by
  refine ⟨by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv⟩

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
private theorem all_coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  exact same ▸ coherent
private theorem all_active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  exact same ▸ active
private theorem all_domains : ∀ own ∈ records, ∀ path ∈ own.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs := by
  intro own member
  have same : own = record := by simpa only [records,List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  exact same ▸ domains
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
private theorem class_room : SourceCurrentAllocatedNativeResourceForecast.Room bits
    (SourceCurrentConstrainedCapClassForecast.classProfile record inputs.length profile) := by
  apply width_room.mono
  change SourceCurrentAllocatedNativeResourceForecast.Le
    (SourceCurrentConstrainedCapClassForecast.classProfile record inputs.length profile)
    (SourceCurrentConstrainedCapClassForecast.classProfile record inputs.length
      (SourceCurrentConstrainedCapClassForecast.classProfile record inputs.length profile))
  exact SourceCurrentConstrainedCapClassForecast.class_ge record inputs.length _
private theorem fold_reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records inputs.length profile :=
  width_room
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : Memo) := by
  intro ambient key entry absent
  cases absent
private theorem first_annotations : SourceEqualityAnnotationLanguage.Annotated
    (fun guard => guard = top ∨ guard = guardA) first := by
  obtain ⟨value,state,done,_guards,annotated⟩ := SourceEqualityAnnotationConstruction.closed
    (fun guard => guard = top ∨ guard = guardA) (wrapper guardA)
    (by simp [wrapper,inner,leaf,SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed])
  have literal : InternedFreshOrdinaryConstruction.build (wrapper guardA) [] empty =
      .done first (InternedFreshOrdinaryConstruction.build (wrapper guardA) [] empty).state := by cbv
  have same : value = first := (InternedNestedConstruction.Outcome.done.inj (done.symm.trans literal)).1
  exact same ▸ annotated
private theorem row_occurrence : SourceCurrentRequiredRowOrigins.RowAt result [.child 0 0] 0 row :=
  .child 0 0 parentRow child output_facts.2.2.2.1 output_facts.2.2.2.2.1 (.root output_facts.2.2.2.2.2.1)
private theorem no_original : ¬∃ path index original, SourceCurrentRequiredRowOrigins.RowAt first path index original ∧
    SourceCurrentRequiredGuardOrigins.RowOrigin original row := by
  rintro ⟨path,index,original,occurrence,fields⟩
  have named := occurrence.annotated first_annotations
  have bad : guardAB = top ∨ guardAB = guardA := by
    simpa only [← fields.1,output_facts.2.2.2.2.2.2] using named
  rcases bad with bad | bad
  · have different : guardAB ≠ top := by decide
    exact different bad
  · have different : guardAB ≠ guardA := by decide
    exact different bad
private theorem class_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ final, ∃ actual : SourceCurrentAllocatedClassEdits.Class record inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty classValues classed.state classed.memo,
      SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual EndpointMemoGateTrace.empty final := by
  obtain ⟨_next,final,actual,reads,_receipt,_frame,_fits,_length⟩ :=
    SourceCurrentActualClassSemanticReads.class_reads formulas solver inventory record coherent active inputs
      (before (bits+2)) SourceCurrentMemoMergeGraph.empty profile (initial_frame formulas solver) initial_fits available
      domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) class_room class_done
  exact ⟨final,actual,reads⟩
private theorem fold_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records inputs (before (bits+2))
      SourceCurrentMemoMergeGraph.empty outputs called.state called.memo,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual EndpointMemoGateTrace.empty final := by
  obtain ⟨_next,final,actual,reads,_receipt,_frame,_fits,_length⟩ :=
    SourceCurrentActualClassSemanticReads.fold_reads formulas solver inventory records all_coherent all_active inputs
      (before (bits+2)) SourceCurrentMemoMergeGraph.empty profile (initial_frame formulas solver) initial_fits available
      all_domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) fold_reserved called_done
  exact ⟨final,actual,reads⟩
end MicroCFTA.ClassFoldStructuralKernels
