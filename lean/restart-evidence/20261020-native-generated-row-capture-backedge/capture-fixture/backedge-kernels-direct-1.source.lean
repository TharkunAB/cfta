import MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# Actual generated Mu with a shared initial inner capture

This calculation checks a new union-body source family.
The actual native generator must create a used outer full Mu.
The candidate shared inner Mu remains an initial leaf capture.
-/
noncomputable section
namespace MicroCFTA.GeneratedRowCaptureBackedgeFixture
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
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 2048
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 1024 :=
  BitVec.ofNatLT (n % 2^1024) (Nat.mod_lt _ (Nat.two_pow_pos 1024))
private theorem word_small (n : Nat) : BitVec.ofNat 1024 n = concreteWord n := by
  apply BitVec.eq_of_toNat_eq
  rfl
attribute [local cbv_eval] word_small
private theorem direct_add (first second : Nat) : Nat.add first second = first + second := rfl
private theorem direct_mul (first second : Nat) : Nat.mul first second = first * second := rfl
private theorem direct_sub (first second : Nat) : Nat.sub first second = first - second := rfl
private theorem direct_div (first second : Nat) : Nat.div first second = first / second := rfl
private theorem direct_mod (first second : Nat) : Nat.mod first second = first % second := rfl
attribute [local cbv_eval] direct_add direct_mul direct_sub direct_div direct_mod
private def top : Guard := SourceEqualityConstraintConstructors.top
private def inner (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("innerRec",.top) top [.var 0],.mk (label,.top) top []])
private def recursive (label innerLabel : String) : Syntax Symbol Guard :=
  .binder false (.union [.node [.mk ("outerRec",.top) top [.var 0],.mk (label,.top) top []],inner innerLabel])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "outerLeft" "tag17",recursive "outerRight" "tag17"]]
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
private def fuel : Nat := 60
private theorem located_fuel : locate 256 0 control before = fuel := by cbv
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
private def muLeaf : Node → Bool := fun value => match value with | .mu .. => true | _ => false
private def captureIndex : Nat := (leaves siteBody).findIdx muLeaf
private def captured : Node := (leaves siteBody)[captureIndex]?.getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey := match captured with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match captured with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match captured with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match captured with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem actual_tag : optionalTag outerRun outerPair := by cbv
private theorem actual_prefix : outerRun = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current :=
  optional_rebuild outerRun outerPair actual_tag
private theorem found : (leaves siteBody)[captureIndex]? = some (.mu entry stored depth ordinary) := by cbv
private theorem initial_capture : heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self
private theorem bounded : 0 < fuel ∧ fuel < 256 := by constructor <;> cbv

private def generatedRun := SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody current.native.machine.heap
private def generated : Node := match generatedRun with | .done value _ => value | .pending .. => .empty
private def generatedHeap : Heap := generatedRun.state
private def generatedEntry : Interned InternedBinderProtocol.NodeKey := match generated with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def generatedBody : Node := match generated with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def generatedDepth : Node := match generated with | .mu _ _ probe _ => probe | _ => .empty
private def generatedOrdinary : Node := match generated with | .mu _ _ _ probe => probe | _ => .empty
private theorem generated_done : generatedRun = .done generated generatedHeap := by cbv
private theorem generated_shape : generated = .mu generatedEntry generatedBody generatedDepth generatedOrdinary := by cbv
private theorem generated_new : current.native.machine.heap.nodeRecords generatedEntry.key = none ∧
    generatedHeap.nodeRecords generatedEntry.key = some generated := by constructor <;> cbv
private theorem generated_used : Reference.interned generatedEntry.identity ∈ generatedBody.free := by
  cbv
  exact List.mem_cons_self
private theorem capture_index_small : captureIndex = 0 ∨ captureIndex = 1 := by cbv

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
private theorem initial_nodes : heap.nodes.next = 19 := by cbv
private theorem nodes_small : heap.nodes.next < 2^10 := by cbv
private theorem edges_small : heap.edges.next ≤ 2^10 := by cbv
private theorem resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources 1022 heap inventory machine.domains := by
  refine ⟨source_facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed heap source_facts,
    Cache.empty_valid,?_,?_,?_⟩
  · exact Nat.lt_of_lt_of_le nodes_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022))
  · exact Nat.le_trans edges_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022+2))
  · rw [inventory,SourceRecursiveIntersectionSourceInventory.domains_length,initial_nodes]
    change 2^(19+19*19) < 2^1023
    exact Nat.pow_lt_pow_right (by decide) (by decide)
private theorem certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified heap inventory control
    before.native.machine (fun final output => Available final.heap output) :=
  SourceCurrentAllocatedRecursivePrefixCode.request_node heap inventory request machine
    ⟨empty_domain _,left_available,right_available⟩
    (initial_scope heap left right left_original right_original left_available right_available)
    (SourceRecursiveIntersectionSourceInventory.empty_mem heap)


private def generatedExpression : Syntax Symbol Guard :=
  .binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)
private def generatedInputs := leaves siteBody
private theorem support :
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧ SemanticHeap current.native.machine.heap ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
    Context current.native.machine.heap generatedInputs ∧
    InternedFreshOrdinaryConstruction.build generatedExpression generatedInputs current.native.machine.heap =
      .done generated generatedHeap ∧
    SourceCurrentNativeCapturedMuUnfoldRows.Observed generatedExpression generatedInputs
      current.native.machine.heap generatedHeap generatedEntry.key generatedEntry generatedBody
      generatedDepth generatedOrdinary generatedHeap := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  have currentPublished := SourceCurrentNativePublicationTrace.source_trace expression checked.trace rfl
  have selected : generatedHeap.nodeRecords generatedEntry.key =
      some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
    rw [←generated_shape]
    exact generated_new.2
  have atCall : (SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody
      current.native.machine.heap).state.nodeRecords generatedEntry.key =
        some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
    simpa only [←generated_done] using selected
  rcases SourceCurrentNativeMuOptionalGeneration.maybeMu outerPair siteBody current.native.machine.heap
      currentPublished.1 available generatedEntry.key generatedEntry generatedBody generatedDepth generatedOrdinary
      atCall with prior | produced
  · rw [generated_new.1] at prior
    cases prior
  · obtain ⟨used,context,compiled,written⟩ := produced
    have actualBuild := compiled.symm.trans generated_done
    have actualWriter : Written generatedExpression generatedInputs current.native.machine.heap generatedHeap
        generatedEntry.key (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
      simpa only [generated_done,InternedNestedConstruction.Outcome.state] using written
    have storedReceipt := SourceCurrentNativeRootedMuStoredRows.of_written generatedExpression generatedInputs
      current.native.machine.heap generatedHeap generatedEntry.key generatedEntry generatedBody generatedDepth
      generatedOrdinary actualWriter
    have generatedSemantic : SemanticHeap generatedHeap := by
      simpa only [generated_done,InternedNestedConstruction.Outcome.state] using
        SourceRecursiveIntersectionSemanticHeap.optionalBinder outerPair siteBody current.native.machine.heap
          currentPublished.1 available
    have generatedAvailable : Available generatedHeap (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
      have verified := InternedFreshOrdinaryFacts.build_verified generatedExpression generatedInputs current.native.machine.heap
        context.base.normal.facts context.base.inputs
      have output := verified.result generated generatedHeap actualBuild
      rw [generated_shape] at output
      exact output
    obtain ⟨interval⟩ := SourceCurrentNativeMuHistory.maybeMu outerPair siteBody current.native.machine.heap
      currentPublished.1 available
    have interval' : SourceCurrentNativeMuPublication.History current.native.machine.heap generatedHeap := by
      simpa only [generated_done,InternedNestedConstruction.Outcome.state] using interval
    obtain ⟨earlier⟩ := currentPublished.2
    have observed := SourceCurrentNativeCapturedMuUnfoldRows.observe generatedExpression generatedInputs
      current.native.machine.heap generatedHeap generatedEntry.key generatedEntry generatedBody generatedDepth
      generatedOrdinary storedReceipt generatedHeap generatedSemantic generatedAvailable (earlier.trans interval')
    exact ⟨checked.trace,available,currentPublished.1,currentPublished.2,context,actualBuild,observed⟩

private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("missing",.top) top []) (empty : Heap)).1
private def tagRow (row : EdgeValue Symbol Guard) : Bool := row.entry.key.symbol == ("tag17",.top)
private def storedRowIndex := (InternedEdgeResidency.nodeEdges stored).findIdx tagRow
private def storedRow := (InternedEdgeResidency.nodeEdges stored)[storedRowIndex]?.getD fallback
private def members : Node → List Node
  | .union _ values _ _ => values
  | _ => []
private def memberIndex := (members generatedBody).findIdx muLeaf
private theorem row_lookup : (InternedEdgeResidency.nodeEdges stored)[storedRowIndex]? = some storedRow := by cbv
private theorem row_fields : storedRow.entry.key.symbol = ("tag17",.top) ∧
    storedRow.entry.key.constraint = top ∧ storedRow.children = [] := by constructor <;> (try constructor) <;> cbv
private theorem row_at {value : Node} {row : EdgeValue Symbol Guard} {index : Nat}
    (found : (InternedEdgeResidency.nodeEdges value)[index]? = some row) : RowAt value row := by
  cases value with
  | node => exact .node found
  | empty | reference | union | mu => simp only [InternedEdgeResidency.nodeEdges,List.getElem?_nil] at found; cases found
private theorem member_at {value atom : Node} {row : EdgeValue Symbol Guard} {index : Nat}
    (found : (members value)[index]? = some atom) (inside : RowAt atom row) : RowAt value row := by
  cases value with
  | union => exact .union found inside
  | empty | reference | node | mu => simp only [members,List.getElem?_nil] at found; cases found
private theorem generated_row : RowAt generatedBody storedRow := by
  apply member_at (index := memberIndex) (atom := .mu entry stored depth ordinary)
  · cbv
  · exact .mu (row_at row_lookup)
private theorem encoded_shape : encode generatedInputs [.intersection outerPair.1 outerPair.2] siteBody =
    .union [.node [.mk ("outerRec",.top) top [.var 0]],.var 2] := by cbv
private theorem actual_index : captureIndex = 1 := by cbv

end MicroCFTA.GeneratedRowCaptureBackedgeFixture
