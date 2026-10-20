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
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentNativeOriginalPublicationTrace (events)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
open InternedEdgeResidency (nodeEdges)
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
  have done : SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody current.native.machine.heap =
      .done generated generatedHeap := generated_done
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
    simpa only [done,InternedNestedConstruction.Outcome.state] using selected
  rcases SourceCurrentNativeMuOptionalGeneration.maybeMu outerPair siteBody current.native.machine.heap
      currentPublished.1 available generatedEntry.key generatedEntry generatedBody generatedDepth generatedOrdinary
      atCall with prior | produced
  · rw [generated_new.1] at prior
    cases prior
  · obtain ⟨used,context,compiled,written⟩ := produced
    have actualBuild := compiled.symm.trans generated_done
    have actualWriter : Written generatedExpression generatedInputs current.native.machine.heap generatedHeap
        generatedEntry.key (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
      simpa only [done,InternedNestedConstruction.Outcome.state] using written
    have storedReceipt := SourceCurrentNativeRootedMuStoredRows.of_written generatedExpression generatedInputs
      current.native.machine.heap generatedHeap generatedEntry.key generatedEntry generatedBody generatedDepth
      generatedOrdinary actualWriter
    have generatedSemantic : SemanticHeap generatedHeap := by
      simpa only [done,InternedNestedConstruction.Outcome.state] using
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
      simpa only [done,InternedNestedConstruction.Outcome.state] using interval
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

private def sourceEdges : List (InternedNestedConstruction.EdgeSyntax Symbol Guard) :=
  [.mk ("outerRec",.top) top [.var 0]]
private def sourceBody : Syntax Symbol Guard := .union [.node sourceEdges,.var 2]
private theorem node_no_binder {inputs captures : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path (.node sourceEdges) inputs (.binder smart body) captures crossings) : False := by
  cases path with
  | node edge member nested =>
    simp only [sourceEdges,List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    simp only [List.mem_singleton] at member
    subst_vars
    cases nested
private theorem body_no_binder {inputs captures : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path sourceBody inputs (.binder smart body) captures crossings) : False := by
  cases path with
  | union member nested =>
    simp only [List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact node_no_binder nested
    · cases nested
private theorem binder_path {inputs captures : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path generatedExpression inputs (.binder smart body) captures crossings) :
    Syntax.binder smart body = generatedExpression := by
  have generatedShape : generatedExpression = .binder true sourceBody := by
    exact congrArg (Syntax.binder true) encoded_shape
  rw [generatedShape] at path
  generalize sourceSame : Syntax.binder true sourceBody = source at path
  cases path with
  | here => exact sourceSame.symm.trans generatedShape.symm
  | node | union => cases sourceSame
  | binder crossing nested =>
    have same : crossing.body = sourceBody := (Syntax.binder.inj sourceSame).2.symm
    rw [same] at nested
    exact (body_no_binder nested).elim
private theorem node_path {inputs captures : List Node} {rows}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path (.node sourceEdges) inputs (.node rows) captures crossings) : rows = sourceEdges := by
  generalize sourceSame : Syntax.node sourceEdges = source at path
  cases path with
  | here => exact (Syntax.node.inj sourceSame).symm
  | binder | union => cases sourceSame
  | node edge member nested =>
    cases sourceSame
    simp only [sourceEdges,List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    simp only [List.mem_singleton] at member
    subst_vars
    cases nested
private theorem body_node_path {inputs captures : List Node} {rows}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path sourceBody inputs (.node rows) captures crossings) : rows = sourceEdges := by
  cases path with
  | union member nested =>
    simp only [List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact node_path nested
    · cases nested
private theorem generated_node_path {inputs captures : List Node} {rows}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path generatedExpression inputs (.node rows) captures crossings) : rows = sourceEdges := by
  have generatedShape : generatedExpression = .binder true sourceBody := congrArg (Syntax.binder true) encoded_shape
  rw [generatedShape] at path
  cases path with
  | binder crossing nested => exact body_node_path nested
private theorem recovered_body {event : @Publication Symbol Guard _}
    (reached : Reached generatedExpression generatedInputs (.binder event.smart event.expression)
      event.environment event.before) : event.expression = sourceBody := by
  obtain ⟨crossings,path,_⟩ := reached
  have same := binder_path path
  have generatedShape : generatedExpression = .binder true sourceBody := congrArg (Syntax.binder true) encoded_shape
  exact (Syntax.binder.inj (same.trans generatedShape)).2
private theorem no_terminal_node {expressions inputs start raw after}
    (reached : Reached generatedExpression generatedInputs (.node expressions) inputs start)
    (source : SourceRow (.node expressions) inputs start raw after storedRow) : False := by
  obtain ⟨crossings,path,_⟩ := reached
  have same := generated_node_path path
  cases same
  cases source with
  | node built made selected call output =>
    have fields := call.source
    have member := List.mem_of_getElem? fields
    simp only [sourceEdges,List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at member
    obtain ⟨rfl,rfl,rfl⟩ := member
    have symbol := output ▸ call.symbol_eq
    rw [row_fields.1] at symbol
    cases symbol
private theorem no_terminal_binder {smart body inputs start event}
    (reached : Reached generatedExpression generatedInputs (.binder smart body) inputs start)
    (eventBody : event = sourceBody)
    (bound : SourceCurrentNativeOriginalObservedResume.SyntaxBound (.binder smart body) event) : False := by
  obtain ⟨crossings,path,_⟩ := reached
  have same := binder_path path
  have generatedShape : generatedExpression = .binder true sourceBody := congrArg (Syntax.binder true) encoded_shape
  rw [same,generatedShape,eventBody] at bound
  simp only [SourceCurrentNativeOriginalObservedResume.SyntaxBound,InternedNestedConstruction.Syntax.binder.sizeOf_spec] at bound
  omega
private theorem pool_shape : generatedInputs =
    [.reference (.intersection outerPair.1 outerPair.2),.mu entry stored depth ordinary] := by cbv
private theorem pool_row {index : Nat} {value : Node}
    (selected : generatedInputs[index]? = some value) (inside : RowAt value storedRow) :
    index = 1 ∧ value = .mu entry stored depth ordinary := by
  rw [pool_shape] at selected
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
    cases selected
    cases inside
  | succ index =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at selected
      exact ⟨rfl,selected.symm⟩
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected

private theorem node_variable_path {inputs captures : List Node} {slot : Nat}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path (.node sourceEdges) inputs (.var slot) captures crossings) : slot = 0 := by
  cases path with
  | node edge member nested =>
    simp only [sourceEdges,List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    simp only [List.mem_singleton] at member
    subst_vars
    cases nested
    rfl
private theorem variable_path {inputs captures : List Node} {slot : Nat}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path generatedExpression inputs (.var slot) captures crossings) :
    slot = 0 ∨ slot = 2 := by
  have generatedShape : generatedExpression = .binder true sourceBody := congrArg (Syntax.binder true) encoded_shape
  rw [generatedShape] at path
  cases path with
  | binder crossing nested =>
    cases nested with
    | union member nested =>
      simp only [List.mem_cons,List.mem_singleton] at member
      rcases member with rfl | rfl
      · exact .inl (node_variable_path nested)
      · cases nested
        exact .inr rfl

private theorem checked_witness :
    build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    locate 256 0 control before = 60 ∧ fuel = 60 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    Reference.interned generatedEntry.identity ∈ generatedBody.free ∧
    storedRow.entry.key.symbol = ("tag17",.top) ∧ storedRow.entry.key.constraint = top ∧ storedRow.children = [] ∧
    RowAt generatedBody storedRow ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody current.native.machine.heap = .done generated generatedHeap ∧
    build (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done generated generatedHeap ∧
    current.native.machine.heap.nodeRecords generatedEntry.key = none ∧
    generatedHeap.nodeRecords generatedEntry.key = some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) ∧
    ∃ event : @Publication Symbol Guard _,
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
        (leaves siteBody) (.binder event.smart event.expression) event.environment event.before ∧
      generatedEntry.key = event.key ∧ generatedEntry = event.entry ∧ generatedBody = event.body ∧
      generatedDepth = event.depth ∧ generatedOrdinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path current.native.machine.heap event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after generatedHeap ∧ Extends event.after.nodes.issued generatedHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
          (leaves siteBody) event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ storedRow, RowAt generatedBody storedRow → RowAt raw storedRow ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter storedRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured storedRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body storedRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ generatedEntry.key ∧
             ((before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry body depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt body storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter generated heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done generated heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next generated)) siteAfter ∧
      Trace suffixFuel (.code (next generated)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done generated heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap))) ∧
        (∃ terminalInputs terminalBefore terminalRaw terminalAfter
          (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)),
          SourceRow (.var 2) terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
          build (.var 2) terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
          Context terminalBefore terminalInputs ∧
          Reached generatedExpression generatedInputs (.var 2) terminalInputs terminalBefore ∧
          SyntaxBound (.var 2) event.expression ∧
          Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
          terminalInputs[2]? = some (.mu entry stored depth ordinary) ∧
          InternedFreshOrdinaryActiveOrigins.Path generatedExpression generatedInputs
            (.var 2) terminalInputs crossings ∧ crossings.length = 1 ∧
          generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
          RowAt stored storedRow ∧ Available current.native.machine.heap (.mu entry stored depth ordinary) ∧
          current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
          entry.key ≠ generatedEntry.key ∧
before.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry stored depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ stored = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt stored storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry stored depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry stored depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt stored storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu generatedEntry generatedBody generatedDepth generatedOrdinary)
            generatedHeap = .done value after →
          SemanticHeap after ∧ Grows generatedHeap after ∧ Extends generatedHeap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
          ∃ originalRow, RowAt generatedBody originalRow ∧
            row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧
            row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter originalRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured originalRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body originalRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ generatedEntry.key ∧
             ((before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after originalRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some originalRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = originalRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry body depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt body storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter generated heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done generated heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next generated)) siteAfter ∧
      Trace suffixFuel (.code (next generated)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done generated heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap)) := by
  obtain ⟨trace,available,semantic,published,context,gBuild,observed⟩ := support
  have selected : generatedHeap.nodeRecords generatedEntry.key =
      some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
    rw [←generated_shape]
    exact generated_new.2
  obtain ⟨called,builtG,missing,present,event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,
      unrecorded,startPath,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,rawBuilt,filtered,
      callbackContext,callbackReached,rows,unfolds⟩ :=
    SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge expression root request fuel
      before current outerPair siteBody siteNext built_done good history trace available generated generatedHeap
      generated_done gBuild generatedEntry generatedBody generatedDepth generatedOrdinary generated_new.1 selected
      generatedHeap observed
  have eventBody := recovered_body reached
  obtain ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,terminalBuild,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,cases⟩ :=
    rows storedRow generated_row
  rcases cases with ⟨expressions,same⟩ | ⟨smart,body,same⟩ | capturedFacts
  · rw [same] at terminalSource terminalReached
    exact (no_terminal_node terminalReached terminalSource).elim
  · rw [same] at terminalReached bound
    exact (no_terminal_binder terminalReached eventBody bound).elim
  · obtain ⟨slot,captured,crossings,originalSlot,same,slotLookup,inside,path,offset,poolLookup,closedCapture,backedge⟩ := capturedFacts
    obtain ⟨rfl,rfl⟩ := pool_row poolLookup inside
    have choices := variable_path path
    have slotSame : slot = 2 := by omega
    subst slot
    have crossingLength : crossings.length = 1 := by omega
    rw [same] at terminalSource terminalBuild terminalReached bound
    obtain ⟨storedInside,captureAvailable,captureResident,different,origin⟩ := backedge entry stored depth ordinary rfl
    rcases origin with initialOrigin | earlier
    · refine ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,good,history,located_fuel,rfl,
        actual_prefix,trace,available,?_,initial_capture.1,initial_capture.2.2,generated_used,
        row_fields.1,row_fields.2.1,row_fields.2.2,generated_row,called,builtG,missing,present,
        event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,startPath,depthPath,
        ordinaryPath,bodyPath,growth,issued,raw,rawAfter,rawBuilt,filtered,callbackContext,callbackReached,
        rows,?_,unfolds⟩
      · simpa only [←actual_index] using found
      · exact ⟨terminalInputs,terminalBefore,terminalRaw,terminalAfter,crossings,terminalSource,terminalBuild,
          terminalContext,terminalReached,bound,suffix,suffixIssued,slotLookup,path,crossingLength,poolLookup,
          storedInside,captureAvailable,captureResident,different,initialOrigin⟩
    · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,otherHeap,
        count,less,earlierTrace,earlierSemantic,parentAvailable,executed,advanced,one,laterTrace,
        absent,recorded,prefixGrowth,rest⟩ := earlier
      have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1
      rw [absent] at retained
      cases retained

/-- The actual generated callback reaches its shared initial used Mu through the same selected capture and original node row call. -/
theorem actual_generated_initial_capture_backedge :
    build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    locate 256 0 control before = 60 ∧ fuel = 60 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    Reference.interned generatedEntry.identity ∈ generatedBody.free ∧
    storedRow.entry.key.symbol = ("tag17",.top) ∧ storedRow.entry.key.constraint = top ∧ storedRow.children = [] ∧
    RowAt generatedBody storedRow ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody current.native.machine.heap = .done generated generatedHeap ∧
    build (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done generated generatedHeap ∧
    current.native.machine.heap.nodeRecords generatedEntry.key = none ∧
    generatedHeap.nodeRecords generatedEntry.key = some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) ∧
    ∃ event : @Publication Symbol Guard _,
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
        (leaves siteBody) (.binder event.smart event.expression) event.environment event.before ∧
      generatedEntry.key = event.key ∧ generatedEntry = event.entry ∧ generatedBody = event.body ∧
      generatedDepth = event.depth ∧ generatedOrdinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path current.native.machine.heap event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after generatedHeap ∧ Extends event.after.nodes.issued generatedHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody))
          (leaves siteBody) event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ storedRow, RowAt generatedBody storedRow → RowAt raw storedRow ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter storedRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured storedRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body storedRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ generatedEntry.key ∧
             ((before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry body depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt body storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter generated heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done generated heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next generated)) siteAfter ∧
      Trace suffixFuel (.code (next generated)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done generated heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap))) ∧
        (∃ terminalInputs terminalBefore terminalRaw terminalAfter
          (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)),
          SourceRow (.var 2) terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
          build (.var 2) terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
          Context terminalBefore terminalInputs ∧
          Reached generatedExpression generatedInputs (.var 2) terminalInputs terminalBefore ∧
          SyntaxBound (.var 2) event.expression ∧
          Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
          terminalInputs[2]? = some (.mu entry stored depth ordinary) ∧
          InternedFreshOrdinaryActiveOrigins.Path generatedExpression generatedInputs
            (.var 2) terminalInputs crossings ∧ crossings.length = 1 ∧
          generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
          RowAt stored storedRow ∧ Available current.native.machine.heap (.mu entry stored depth ordinary) ∧
          current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
          entry.key ≠ generatedEntry.key ∧
before.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry stored depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ stored = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt stored storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry stored depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry stored depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt stored storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu generatedEntry generatedBody generatedDepth generatedOrdinary)
            generatedHeap = .done value after →
          SemanticHeap after ∧ Grows generatedHeap after ∧ Extends generatedHeap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
          ∃ originalRow, RowAt generatedBody originalRow ∧
            row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧
            row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter originalRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured originalRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection outerPair.1 outerPair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body originalRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ generatedEntry.key ∧
             ((before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached expression [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached expression [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached expression [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
            ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after originalRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some originalRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = originalRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry body depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt body storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter generated heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done generated heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next generated)) siteAfter ∧
      Trace suffixFuel (.code (next generated)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done generated heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap)) := checked_witness

end MicroCFTA.GeneratedRowCaptureBackedgeFixture
