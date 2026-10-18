import MicroCFTA.SourceCurrentNativePositiveRowOrigins
import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceCurrentNativeRowKeyable
import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceEqualityNormalizationReceipt
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.NativePositiveRowKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def first : Syntax Symbol Guard := .node [.mk ("pair",.top) top [leaf,leaf]]
private def second : Syntax Symbol Guard := .node [.mk ("pair",.top) own [leaf,leaf]]
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [first,second]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def firstAllocation := SourceEqualityConstraintAllocation.construct top.equalities Cache.emptyState
private def firstValue := match firstAllocation.1 with | .ok value => value | .error _ => .contradiction
private def secondAllocation := SourceEqualityConstraintAllocation.construct own.equalities firstAllocation.2
private def secondValue := match secondAllocation.1 with | .ok value => value | .error _ => .contradiction
private def before : Checked 130 :=
  ⟨initial 130 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial secondAllocation.2⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain left right)
private noncomputable def cold := execute 64 control before
private noncomputable def output : Node := match cold with | .done value _ => value | _ => .empty
private noncomputable def after := cold.state
private noncomputable def row : Row := (nodeEdges output)[0]?.getD (run (makeEdge ("fallback",.top) top []) heap).1
private noncomputable def child : Node := row.children[0]?.getD .empty
private theorem built_done : built = .done root heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have cached : SourceEqualityGuardReadback.Cached own.equalities := by
    intro classes same
    cases same
    exact SourceEqualityGuardReadback.normalized
      (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
  have firstHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [top] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show firstAllocation = (.ok firstValue,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState secondAllocation.2 [top,own] :=
    SourceEqualityOriginalAllocationHistory.History.construct firstHistory cached
      (show secondAllocation = (.ok secondValue,secondAllocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [top,own] := by
    intro guard member
    simpa only [expression,first,second,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self,
      or_left_comm,or_comm,or_assoc] using member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 130 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem initial_good : Good before := initial_ready.good
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private theorem cold_done : cold = .done output after := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases actual : cold <;> simp_all only [output,after,Outcome.state,Bool.false_eq_true]
private theorem warm_done : execute 2 control after = .done output after := by cbv
private theorem selected : (nodeEdges output)[0]? = some row := by cbv
private theorem child_selected : row.children[0]? = some child := by cbv
private theorem positive : ¬ Plain row.entry.key.constraint := by cbv
private theorem branch : SourceRecursiveIntersectionControl.decision request.domain.key left right = .ordinary := by cbv

private theorem checked_witness :
    ∃ (program : Syntax Symbol Guard) (input : Node) (source : State Symbol Guard)
      (initial final : Checked 130) (left right result : Node) (row : Row) (child : Node),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input source ∧
      initial.native.machine.heap = source ∧ Good initial ∧
      Available source left ∧ Available source right ∧ left ≠ right ∧
      SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key left right = .ordinary ∧
      execute 64 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) initial = .done result final ∧
      execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) final = .done result final ∧
      History final ∧ (nodeEdges result)[0]? = some row ∧ row.children[0]? = some child ∧
      ¬ Plain row.entry.key.constraint ∧
      ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : Row)
        (leftChild rightChild : Node) (callBefore callAfter : Checked 130) (fuel : Nat),
        (nodeEdges left)[leftIndex]? = some leftRow ∧ (nodeEdges right)[rightIndex]? = some rightRow ∧
        Plain leftRow.entry.key.constraint ∧ ¬ Plain rightRow.entry.key.constraint ∧
        row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
          leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
        leftRow.children[0]? = some leftChild ∧ rightRow.children[0]? = some rightChild ∧
        InternedValueMass.value leftChild < InternedValueMass.value left ∧
        InternedValueMass.value rightChild < InternedValueMass.value right ∧
        Good callBefore ∧ Good callAfter ∧
        Grows callBefore.native.machine.heap final.native.machine.heap ∧
        Grows callAfter.native.machine.heap final.native.machine.heap ∧
        Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain leftChild rightChild))
          callBefore (.code (.pure child)) callAfter := by
  obtain ⟨count,_,traced,_,_,_⟩ := SourceCurrentNativeKeyAdmission.node_done 128 64 before initial_good
    initial_ready.semantic left right available.1 available.2 (by cbv) (by cbv)
    (by cbv) (by cbv) (by cbv) cold_done
  have history : History after := (History.initial ⟨heap,Cache.emptyState⟩ before.operations).query
    request count output initial_good traced
  have keyed := SourceCurrentNativeRowKeyable.selected request count output traced 0 row selected
  obtain ⟨_,_,_,_,_,cellKey⟩ := keyed
  obtain ⟨_,_,_,origin⟩ := SourceCurrentSharedLeafNativeLineage.request request count output
    initial_good (History.initial ⟨heap,Cache.emptyState⟩ before.operations) traced
  obtain ⟨handle,returned⟩ : ∃ handle,after.native.nodes.cells handle = some ⟨request,.returned output⟩ := by
    rcases origin with ⟨missing,_⟩ | ⟨handle,present,_⟩
    · rw [cellKey] at missing; cases missing
    · exact ⟨handle,present⟩
  obtain ⟨le,lrows,ld,lf,leftShape⟩ : ∃ entry rows depth free,left = .node entry rows depth free := by
    cases shape : left with
    | node entry rows depth free => exact ⟨entry,rows,depth,free,shape⟩
    | empty | reference | union | mu => cbv at shape; cases shape
  obtain ⟨re,rrows,rd,rf,rightShape⟩ : ∃ entry rows depth free,right = .node entry rows depth free := by
    cases shape : right with
    | node entry rows depth free => exact ⟨entry,rows,depth,free,shape⟩
    | empty | reference | union | mu => cbv at shape; cases shape
  obtain ⟨li,ri,lr,rr,_,lc,rc,cb,ca,fuel,foundLeft,foundRight,_,_,_,guard,
      positiveSide,firstChild,secondChild,firstMass,secondMass,firstGood,lastGood,firstGrowth,lastGrowth,called⟩ :=
    SourceCurrentNativePositiveRowOrigins.positive_child history handle request output returned
      le re lrows rrows ld rd lf rf leftShape rightShape branch 0 row selected positive 0 child child_selected
  have firstPlain : Plain lr.entry.key.constraint := by
    have member := List.mem_of_getElem? foundLeft
    have singleton : nodeEdges request.left = [(nodeEdges left)[0]?.getD row] := by cbv
    rw [singleton] at member
    rw [List.mem_singleton.mp member]
    cbv
  have secondPositive : ¬ Plain rr.entry.key.constraint := by
    rcases positiveSide with impossible | actual
    · exact (impossible firstPlain).elim
    · exact actual
  refine ⟨expression,root,heap,before,after,left,right,output,row,child,built_done,rfl,initial_good,
    available.1,available.2,?_,branch,cold_done,warm_done,history,selected,child_selected,positive,
    li,ri,lr,rr,lc,rc,cb,ca,fuel,foundLeft,foundRight,firstPlain,secondPositive,guard,firstChild,
    secondChild,firstMass,secondMass,firstGood,lastGood,firstGrowth,lastGrowth,called⟩
  intro same
  have identities := congrArg Value.referenceOf same
  cbv at identities
  cases identities

end MicroCFTA.NativePositiveRowKernels
