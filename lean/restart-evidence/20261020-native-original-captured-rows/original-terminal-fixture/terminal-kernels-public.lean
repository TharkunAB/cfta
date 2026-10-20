import MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows
import MicroCFTA.SourceCurrentNativeOriginalObservedTerminals
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An initial shared Mu retains its original source terminals

Two distinct outer binders share the same closed used inner Mu.
The actual outer optional captures that initial Mu at leaf occurrence one.
Its actual unfold row retains one original source publication and callback.
The same stored and observed rows retain their source terminal suffixes.
-/
noncomputable section
namespace MicroCFTA.OriginalCapturedTerminalFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (Row)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 1024 :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h (by decide : 1024 ≤ 2^1024))
  else BitVec.ofNat 1024 n
private theorem word_small (n : Nat) : BitVec.ofNat 1024 n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^1024 = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) (by decide : 1024 ≤ 2^1024))
  · rfl
attribute [local cbv_eval] word_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def inner (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("rec",.top) top [.var 0],.mk (label,.top) top []])
private def recursive (label innerLabel : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("outer",.top) top [.var 0,inner innerLabel],.mk (label,.top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "outerLeft" "sharedInner",recursive "outerRight" "sharedInner"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def allocatedOps := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def before : Checked 1024 := ⟨initial 1024 machine,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain request.left request.right)
private def outerPair := SourceRecursiveIntersectionControl.pair
  ((SourceRecursiveIntersectionControl.identity left).getD 0) ((SourceRecursiveIntersectionControl.identity right).getD 0)
private def locate : Nat → Nat → Control Node → Checked 1024 → Nat
  | 0, elapsed, _, _ => elapsed
  | remaining+1, elapsed, input, state =>
      match input with
      | .code (.optionalBinder pair _ _) =>
          match pair == outerPair with
          | true => elapsed
          | false => match step input state with
              | .yielded next after => locate remaining (elapsed+1) next after
              | _ => elapsed
      | _ => match step input state with
          | .yielded next after => locate remaining (elapsed+1) next after
          | _ => elapsed
private def fuel := locate 128 0 control before
private def outerRun := execute fuel control before
private def current : Checked 1024 := outerRun.state
private def bodyOf : Outcome 1024 Node → Node
  | .yielded (.code (.optionalBinder _ bodyValue _)) _ => bodyValue | _ => .empty
private def nextOf : Outcome 1024 Node → (Node → Code Symbol Guard Node)
  | .yielded (.code (.optionalBinder _ _ next)) _ => next | _ => .pure
private def optionalTag : Outcome 1024 Node → (Nat × Nat) → Prop
  | .yielded (.code (.optionalBinder pair _ _)) _,expected => pair = expected
  | _,_ => False
private theorem optional_rebuild (observation : Outcome 1024 Node) (expected : Nat × Nat)
    (tag : optionalTag observation expected) :
    observation = .yielded (.code (.optionalBinder expected (bodyOf observation) (nextOf observation))) observation.state := by
  cases observation with
  | yielded reached state =>
      cases reached with
      | edgeBody => cases tag
      | code code => cases code <;> simp_all [optionalTag,bodyOf,nextOf,Outcome.state]
  | done | failed | constraintError | blocked => cases tag
private def siteBody : Node := bodyOf outerRun
private def siteNext : Node → Code Symbol Guard Node := nextOf outerRun
private def captured : Node := (leaves siteBody)[1]?.getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey := match captured with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match captured with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match captured with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match captured with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem actual_tag : optionalTag outerRun outerPair := by cbv
private theorem actual_prefix : outerRun = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current :=
  optional_rebuild outerRun outerPair actual_tag
private theorem found : (leaves siteBody)[1]? = some (.mu entry stored depth ordinary) := by cbv
private theorem initial_capture : heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self
private theorem bounded : 0 < fuel ∧ fuel < 128 := by constructor <;> cbv

private theorem source_facts : InternedNestedFacts.Facts heap :=
  (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem root_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem children_shape : children root = [left,right] := by cbv
private theorem left_available : Available heap left :=
  root_available.children left (by rw [children_shape]; simp only [List.mem_cons, true_or])
private theorem right_available : Available heap right :=
  root_available.children right (by rw [children_shape]; simp)
private theorem closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv
private theorem operands_used :
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) := by
  constructor <;> (cbv; exact List.mem_cons_self)
private theorem operands_distinct : left ≠ right := by
  intro same
  have different : (SourceRecursiveIntersectionControl.identity left == SourceRecursiveIntersectionControl.identity right) = false := by cbv
  rw [same] at different
  simp only [beq_self_eq_true] at different
  cases different
private theorem top_field : SourceCurrentConjunctionEquality.FieldAvailable allocatedOps top :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).2.2
private theorem allocated_valid : SourceEqualityConstraintMemoAllocation.Valid allocatedOps :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).1
private theorem fields : SourceCurrentConjunctionEquality.Fields allocatedOps heap := by
  change SourceEqualityAnnotationHeap.Heap (SourceCurrentConjunctionEquality.FieldAvailable allocatedOps)
    (InternedFreshOrdinaryConstruction.build expression [] empty).state
  refine SourceEqualityAnnotationConstruction.build _ expression ?_ [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)
  simp only [expression,recursive,inner,SourceEqualityAnnotationConstruction.Allowed,
    SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed,
    top_field,and_self]
private theorem semantic : SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.constructed expression root heap built_done
private theorem semantic_ready : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem good : SourceCurrentAllocatedNativePhysicalCompletion.Good before := by
  refine ⟨?_,semantic_ready.ready,allocated_valid,fields⟩
  exact SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨source_facts,Cache.empty_valid⟩
private theorem history : SourceCurrentNativeEdgeWriterGrowth.History before := .initial _ _
private theorem left_original : SourceRecursiveIntersectionInputView.Original left :=
  SourceRecursiveIntersectionOriginalOutput.closed_original left heap source_facts.coherent left_available closed.1
private theorem right_original : SourceRecursiveIntersectionInputView.Original right :=
  SourceRecursiveIntersectionOriginalOutput.closed_original right heap source_facts.coherent right_available closed.2
private def inventory := SourceRecursiveIntersectionSourceInventory.domains heap
private theorem initial_nodes : heap.nodes.next = 13 := by cbv
private theorem nodes_small : heap.nodes.next < 2^10 := by cbv
private theorem edges_small : heap.edges.next ≤ 2^10 := by cbv
private theorem resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources 1022 heap inventory machine.domains := by
  refine ⟨source_facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed heap source_facts,
    Cache.empty_valid,?_,?_,?_⟩
  · exact Nat.lt_of_lt_of_le nodes_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022))
  · exact Nat.le_trans edges_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022+2))
  · rw [inventory,SourceRecursiveIntersectionSourceInventory.domains_length,initial_nodes]
    change 2^(13+13*13) < 2^1023
    exact Nat.pow_lt_pow_right (by decide) (by decide)
private theorem certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified heap inventory control
    before.native.machine (fun final output => Available final.heap output) :=
  SourceCurrentAllocatedRecursivePrefixCode.request_node heap inventory request machine
    ⟨empty_domain _,left_available,right_available⟩
    (initial_scope heap left right left_original right_original left_available right_available)
    (SourceRecursiveIntersectionSourceInventory.empty_mem heap)

private def unfoldedRun := InternedFreshOrdinaryStoredSubstitution.unfold
  (.mu entry stored depth ordinary) current.native.machine.heap
private def unfolded : Node := match unfoldedRun with | .done value _ => value | .pending .. => .empty
private def unfoldedHeap : Heap := unfoldedRun.state
private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("missing",.top) top []) (empty : Heap)).1
private def recRow (row : EdgeValue Symbol Guard) : Bool := row.entry.key.symbol == ("rec",.top)
private def unfoldedIndex : Nat := (InternedEdgeResidency.nodeEdges unfolded).findIdx recRow
private def storedIndex : Nat := (InternedEdgeResidency.nodeEdges stored).findIdx recRow
private def unfoldedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]?.getD fallback
private def storedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges stored)[storedIndex]?.getD fallback
private theorem actual_unfold : unfoldedRun = .done unfolded unfoldedHeap := by cbv
private theorem unfolded_selected : (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]? = some unfoldedRow := by cbv
private theorem unfolded_fields : unfoldedRow.entry.key.symbol = ("rec",.top) ∧
    unfoldedRow.entry.key.constraint = top ∧ unfoldedRow.children = [.mu entry stored depth ordinary] := by
  constructor
  · cbv
  constructor <;> cbv
private theorem node_row {value : Node} {row : EdgeValue Symbol Guard}
    (selected : row ∈ InternedEdgeResidency.nodeEdges value) : Row value row := by
  cases value with
  | node => exact .node selected
  | empty | reference | union | mu => cases selected
private theorem stored_children : storedRow.children = [.reference (.interned entry.identity)] := by cbv
private theorem rows_distinct : unfoldedRow ≠ storedRow := by
  intro same
  have different : (unfoldedRow.children.map Value.referenceOf == storedRow.children.map Value.referenceOf) = false := by cbv
  rw [same] at different
  simp only [beq_self_eq_true] at different
  cases different
private theorem stored_rec_unique (row : EdgeValue Symbol Guard) (inside : RowAt stored row)
    (symbol : row.entry.key.symbol = ("rec",.top)) : row = storedRow := by
  have shape : (match stored with | .node .. => True | _ => False) := by cbv
  have filtered : (InternedEdgeResidency.nodeEdges stored).filter recRow = [storedRow] := by cbv
  cases actual : stored with
  | node selected rows level free =>
      rw [actual] at inside filtered
      change rows.filter recRow = [storedRow] at filtered
      cases inside with
      | node found =>
          have member : row ∈ rows.filter recRow := List.mem_filter.mpr
            ⟨List.mem_of_getElem? found,by simp only [recRow,symbol,beq_self_eq_true]⟩
          rw [filtered] at member
          exact List.mem_singleton.mp member
  | empty | reference | union | mu => simp only [actual] at shape

private def outerRow (value : Node) : EdgeValue Symbol Guard :=
  ((InternedEdgeResidency.nodeEdges (body value)).find? (fun row => row.entry.key.symbol == ("outer",.top))).getD fallback
private theorem shared_capture : (outerRow left).children[1]? = some (.mu entry stored depth ordinary) ∧
    (outerRow right).children[1]? = some (.mu entry stored depth ordinary) := by constructor <;> cbv

private theorem checked_witness :
    InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    0 < fuel ∧ fuel < 128 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    (leaves siteBody)[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
    unfoldedRun = .done unfolded unfoldedHeap ∧
    (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]? = some unfoldedRow ∧
    unfoldedRow.entry.key.symbol = ("rec",.top) ∧ unfoldedRow.entry.key.constraint = top ∧
    unfoldedRow.children = [.mu entry stored depth ordinary] ∧
    storedRow.children = [.reference (.interned entry.identity)] ∧ unfoldedRow ≠ storedRow ∧
    (outerRow left).children[1]? = some (.mu entry stored depth ordinary) ∧
    (outerRow right).children[1]? = some (.mu entry stored depth ordinary) ∧
    SemanticHeap unfoldedHeap ∧ Grows current.native.machine.heap unfoldedHeap ∧
    Extends current.native.machine.heap.nodes.issued unfoldedHeap.nodes.issued ∧
    Available unfoldedHeap unfolded ∧ Nonempty (SourceCurrentNativeMuPublication.History empty unfoldedHeap) ∧
      (∃ event : @Publication Symbol Guard _,
    Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
    entry.key = event.key ∧ entry = event.entry ∧ stored = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path empty event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after heap ∧ Extends event.after.nodes.issued heap.nodes.issued ∧
    ∃ raw rawAfter,
      InternedFreshOrdinaryConstruction.build event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached expression [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      (∀ row, RowAt stored row → RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row ∧
          SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter row) ∧
      (∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry stored depth ordinary) current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧ Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
        ∃ original, RowAt stored original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
          row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
          (row = original ∨ ∃ lexical current next, Calls lexical original.children current row.children next) ∧
          RowAt raw original ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter original ∧
              SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter original) ∧
      RowAt stored storedRow ∧
      unfoldedRow.entry.key.symbol = storedRow.entry.key.symbol ∧
      unfoldedRow.entry.key.constraint = storedRow.entry.key.constraint ∧
      unfoldedRow.children.length = storedRow.children.length ∧
      (∃ lexical first last, Calls lexical storedRow.children first unfoldedRow.children last) ∧
      RowAt raw storedRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter storedRow ∧
        SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter storedRow) := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  have currentPublished := SourceCurrentNativePublicationTrace.source_trace expression checked.trace rfl
  rcases SourceCurrentNativeOriginalCapturedMuRows.capture_source expression root request fuel before current
      outerPair siteBody siteNext built_done good history checked.trace available 1 entry stored depth ordinary found
      with capturedInitial | generated
  · obtain ⟨prior,observed⟩ := capturedInitial
    have enriched := SourceCurrentNativeOriginalObservedTerminals.of_observed expression empty
      before.native.machine.heap entry.key entry stored depth ordinary current.native.machine.heap observed
    obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,
      startPath,depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,
      rawBuilt,filtered,callbackContext,callbackReached,storedRows,everyUnfold⟩ := enriched
    obtain ⟨afterSemantic,growth,issued,outputAvailable,published,observedRows⟩ :=
      everyUnfold unfolded unfoldedHeap actual_unfold
    obtain ⟨original,inside,symbol,guard,arity,calls,rawRow,source,terminal⟩ :=
      observedRows unfoldedRow (node_row (List.mem_of_getElem? unfolded_selected))
    have same := stored_rec_unique original inside (symbol.symm.trans unfolded_fields.1)
    subst original
    rcases calls with unchanged | actualCalls
    · exact False.elim (rows_distinct unchanged)
    · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
        operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
        actual_prefix,checked.trace,available,found,prior,initial_capture.2.1,initial_capture.2.2,
        currentPublished.2,actual_unfold,unfolded_selected,unfolded_fields.1,unfolded_fields.2.1,
        unfolded_fields.2.2,stored_children,rows_distinct,shared_capture.1,shared_capture.2,
        afterSemantic,growth,issued,outputAvailable,published,
        event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,startPath,
        depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,rawBuilt,filtered,
        callbackContext,callbackReached,storedRows,everyUnfold,inside,symbol,guard,arity,actualCalls,rawRow,source,terminal⟩
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,after,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,storedCertificate,observe⟩ := generated
    have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1
    rw [missing] at retained
    cases retained

/-- An actual initial Mu capture retains the same original source terminal and changed unfold calls. -/
theorem actual_initial_terminal :
    InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    0 < fuel ∧ fuel < 128 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    (leaves siteBody)[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
    unfoldedRun = .done unfolded unfoldedHeap ∧
    (InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]? = some unfoldedRow ∧
    unfoldedRow.entry.key.symbol = ("rec",.top) ∧ unfoldedRow.entry.key.constraint = top ∧
    unfoldedRow.children = [.mu entry stored depth ordinary] ∧
    storedRow.children = [.reference (.interned entry.identity)] ∧ unfoldedRow ≠ storedRow ∧
    (outerRow left).children[1]? = some (.mu entry stored depth ordinary) ∧
    (outerRow right).children[1]? = some (.mu entry stored depth ordinary) ∧
    SemanticHeap unfoldedHeap ∧ Grows current.native.machine.heap unfoldedHeap ∧
    Extends current.native.machine.heap.nodes.issued unfoldedHeap.nodes.issued ∧
    Available unfoldedHeap unfolded ∧ Nonempty (SourceCurrentNativeMuPublication.History empty unfoldedHeap) ∧
      (∃ event : @Publication Symbol Guard _,
    Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
    entry.key = event.key ∧ entry = event.entry ∧ stored = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path empty event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after heap ∧ Extends event.after.nodes.issued heap.nodes.issued ∧
    ∃ raw rawAfter,
      InternedFreshOrdinaryConstruction.build event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached expression [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      (∀ row, RowAt stored row → RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row ∧
          SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter row) ∧
      (∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry stored depth ordinary) current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧ Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
        ∃ original, RowAt stored original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
          row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
          (row = original ∨ ∃ lexical current next, Calls lexical original.children current row.children next) ∧
          RowAt raw original ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter original ∧
              SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter original) ∧
      RowAt stored storedRow ∧
      unfoldedRow.entry.key.symbol = storedRow.entry.key.symbol ∧
      unfoldedRow.entry.key.constraint = storedRow.entry.key.constraint ∧
      unfoldedRow.children.length = storedRow.children.length ∧
      (∃ lexical first last, Calls lexical storedRow.children first unfoldedRow.children last) ∧
      RowAt raw storedRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter storedRow ∧
        SourceCurrentNativeOriginalObservedTerminals.Terminal expression event.expression rawAfter storedRow) := checked_witness

end MicroCFTA.OriginalCapturedTerminalFixture

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.OriginalCapturedTerminalFixture.actual_initial_terminal
#print MicroCFTA.OriginalCapturedTerminalFixture.actual_initial_terminal
#print axioms MicroCFTA.OriginalCapturedTerminalFixture.actual_initial_terminal
