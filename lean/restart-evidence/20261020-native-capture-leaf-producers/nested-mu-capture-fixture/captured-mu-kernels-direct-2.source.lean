import MicroCFTA.SourceCurrentNativeCapturedMuOrigins
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An outer optional captures an earlier generated full Mu

Two closed source binders contain distinct closed recursive inner binders.
Actual execution stops at the outer pair's optional instruction. Its leaf
pool contains the newly generated inner Mu at occurrence index one.
The initial heap has no record for that selected inner Mu key.
The same capture producer retains the earlier actual generating site.
-/
noncomputable section
namespace MicroCFTA.NestedCapturedMuFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
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
  .node [.mk ("pair",.top) top [recursive "outerLeft" "innerLeft",recursive "outerRight" "innerRight"]]
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
private theorem new_capture : heap.nodeRecords entry.key = none ∧
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
private theorem initial_nodes : heap.nodes.next = 17 := by cbv
private theorem nodes_small : heap.nodes.next < 2^10 := by cbv
private theorem edges_small : heap.edges.next ≤ 2^10 := by cbv
private theorem resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources 1022 heap inventory machine.domains := by
  refine ⟨source_facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed heap source_facts,
    Cache.empty_valid,?_,?_,?_⟩
  · exact Nat.lt_of_lt_of_le nodes_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022))
  · exact Nat.le_trans edges_small (Nat.pow_le_pow_right (by decide) (by decide : 10 ≤ 1022+2))
  · rw [inventory,SourceRecursiveIntersectionSourceInventory.domains_length,initial_nodes]
    change 2^(17+17*17) < 2^1023
    exact Nat.pow_lt_pow_right (by decide) (by decide)
private theorem certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified heap inventory control
    before.native.machine (fun final output => Available final.heap output) :=
  SourceCurrentAllocatedRecursivePrefixCode.request_node heap inventory request machine
    ⟨empty_domain _,left_available,right_available⟩
    (initial_scope heap left right left_original right_original left_available right_available)
    (SourceRecursiveIntersectionSourceInventory.empty_mem heap)

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
    heap.nodeRecords entry.key = none ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done result heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry stored depth ordinary) ∧
      (∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked 1024)
        (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State 1024 Symbol Guard)
        (first second : Nat),
      let compilerBefore : Checked 1024 := ⟨running, queryBefore.operations⟩
      let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
        queried.domain.key queried.left queried.right first second
      let childBefore : Checked 1024 :=
        {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
      prefixFuel = queryFuel + 2 + childFuel ∧
      Trace queryFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.node queried callerNext)) queryBefore ∧
      Inputs (.code (.node queried callerNext)) queryBefore ∧
      lookupNode 1024 queried queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate queried, running) ∧
      chosen.nodes.cells handle = some ⟨queried, .suspended⟩ ∧
      running.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      running.machine = queryBefore.native.machine ∧
      step (.code (.node queried callerNext)) queryBefore = .yielded
        (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
      (SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) ∧
      SourceRecursiveIntersectionControl.identity queried.left = some first ∧
      SourceRecursiveIntersectionControl.identity queried.right = some second ∧
      priorPair = SourceRecursiveIntersectionControl.pair first second ∧
      Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure parent)) siteBefore ∧
      (next = fun value => .finishNode handle value (callerNext value)) ∧
      siteBefore.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩ childBefore siteBefore parent ∧
      ∃ (terminal : NodeRequest Symbol Guard) (terminalHandle : Nat),
        SourceCurrentNativeQueryRowOrigins.Route siteBefore parent
          ⟨entered.1,body queried.left,body queried.right⟩ terminal ∧
        siteBefore.native.nodes.cells terminalHandle = some ⟨terminal,.returned parent⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written terminalHandle terminal parent siteBefore.native ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
        (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
        (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
        terminalHandle ≠ handle) := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  rcases SourceCurrentNativeCapturedMuOrigins.capture request fuel before current outerPair siteBody siteNext
    good history semantic checked.trace available 1 entry stored depth ordinary found with prior | generated
  · change heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) at prior
    rw [new_capture.1] at prior
    cases prior
  · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
      operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
      actual_prefix,checked.trace,available,found,new_capture.1,new_capture.2.1,new_capture.2.2,generated⟩

/-- The exact outer leaf occurrence retains its same earlier generated Mu writer and terminal origin. -/
theorem actual_nested_capture :
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
    heap.nodeRecords entry.key = none ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done result heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry stored depth ordinary) ∧
      (∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked 1024)
        (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State 1024 Symbol Guard)
        (first second : Nat),
      let compilerBefore : Checked 1024 := ⟨running, queryBefore.operations⟩
      let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
        queried.domain.key queried.left queried.right first second
      let childBefore : Checked 1024 :=
        {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
      prefixFuel = queryFuel + 2 + childFuel ∧
      Trace queryFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.node queried callerNext)) queryBefore ∧
      Inputs (.code (.node queried callerNext)) queryBefore ∧
      lookupNode 1024 queried queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate queried, running) ∧
      chosen.nodes.cells handle = some ⟨queried, .suspended⟩ ∧
      running.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      running.machine = queryBefore.native.machine ∧
      step (.code (.node queried callerNext)) queryBefore = .yielded
        (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
      (SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) ∧
      SourceRecursiveIntersectionControl.identity queried.left = some first ∧
      SourceRecursiveIntersectionControl.identity queried.right = some second ∧
      priorPair = SourceRecursiveIntersectionControl.pair first second ∧
      Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure parent)) siteBefore ∧
      (next = fun value => .finishNode handle value (callerNext value)) ∧
      siteBefore.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩ childBefore siteBefore parent ∧
      ∃ (terminal : NodeRequest Symbol Guard) (terminalHandle : Nat),
        SourceCurrentNativeQueryRowOrigins.Route siteBefore parent
          ⟨entered.1,body queried.left,body queried.right⟩ terminal ∧
        siteBefore.native.nodes.cells terminalHandle = some ⟨terminal,.returned parent⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written terminalHandle terminal parent siteBefore.native ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
        (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
        (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
        terminalHandle ≠ handle) := checked_witness

end MicroCFTA.NestedCapturedMuFixture
