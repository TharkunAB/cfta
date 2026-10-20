import MicroCFTA.SourceCurrentNativeOriginGeneration
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# A compiled recursive request installs a new used Mu

Both closed operands retain one recursive row and a distinct nullary row.
Actual checked intersection keeps the common recursive row. Its repeated
pair reference remains free before the optional instruction executes.
The selected full Mu is absent initially and present after execution.
-/
noncomputable section
namespace MicroCFTA.CompiledMuGenerationFixture
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
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 128 :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h (by decide : 1024 ≤ 2^128))
  else BitVec.ofNat 128 n
private theorem word_small (n : Nat) : BitVec.ofNat 128 n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^128 = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) (by decide : 1024 ≤ 2^128))
  · rfl
attribute [local cbv_eval] word_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def recursive (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("rec",.top) top [.var 0],.mk (label,.top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "left",recursive "right"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def allocatedOps := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def before : Checked 128 := ⟨initial 128 machine,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain request.left request.right)
private def result := execute 64 control before
private def value : Node := match result with | .done output _ => output | _ => .empty
private def after : Checked 128 := result.state
private def entry : Interned InternedBinderProtocol.NodeKey := match value with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match value with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match value with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match value with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem returned : result = .done value after := by cbv
private theorem new_mu : value = .mu entry stored depth ordinary ∧
    heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    InternedBinderProtocol.Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self

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
  have identities := congrArg SourceRecursiveIntersectionControl.identity same
  change some 2 = some 6 at identities
  cases identities
private theorem top_field : SourceCurrentConjunctionEquality.FieldAvailable allocatedOps top :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).2.2
private theorem allocated_valid : SourceEqualityConstraintMemoAllocation.Valid allocatedOps :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).1
private theorem fields : SourceCurrentConjunctionEquality.Fields allocatedOps heap := by
  apply SourceEqualityAnnotationConstruction.build _ expression _ [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)
  simp only [expression,recursive,SourceEqualityAnnotationConstruction.Allowed,
    SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed,
    top_field,and_self,and_true,true_and]
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
private theorem resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources 126 heap inventory machine.domains := by
  refine ⟨source_facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed heap source_facts,
    Cache.empty_valid,?_,?_,?_⟩
  · cbv
  · cbv
  · rw [inventory,SourceRecursiveIntersectionSourceInventory.domains_length]
    cbv
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
    execute 64 control before = .done value after ∧ value = .mu entry stored depth ordinary ∧
    heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    ∃ count, count ≤ 64 ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before ∧
      execute count control before = .done value after ∧
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      count = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      call.state.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state entry.key (.mu entry stored depth ordinary) ∧
      SourceCurrentNativeOptionalChildOrigin.Origin request prefixFuel before siteBefore pair siteBody next := by
  obtain ⟨steps,bounded,rawTrace⟩ := done_trace 64 control before after value returned
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources steps control before
    (.code (.pure value)) after (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have plan := checked.trace.plan
  have completed := trace_done steps control before after value rawTrace
  have selected : (execute (steps+1) control before).state.native.machine.heap.nodeRecords entry.key =
      some (.mu entry stored depth ordinary) := by
    rw [completed]
    exact new_mu.2.2.1
  rcases SourceCurrentNativeOriginGeneration.execute request plan good history semantic entry.key entry
    stored depth ordinary selected with prior | generated
  · rw [new_mu.2.1] at prior
    cases prior
  · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
      operands_used.1,operands_used.2,good,history,returned,new_mu.1,new_mu.2.1,
      new_mu.2.2.1,new_mu.2.2.2,steps+1,by omega,plan,completed,generated⟩

/-- Actual recursive compilation produces one new used Mu with its same owner and rooted writer. -/
theorem actual_compiled_generation :
    InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    execute 64 control before = .done value after ∧ value = .mu entry stored depth ordinary ∧
    heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    ∃ count, count ≤ 64 ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before ∧
      execute count control before = .done value after ∧
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      count = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      call.state.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count (.code (requestNode request.domain request.left request.right)) before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state entry.key (.mu entry stored depth ordinary) ∧
      SourceCurrentNativeOptionalChildOrigin.Origin request prefixFuel before siteBefore pair siteBody next := checked_witness

end MicroCFTA.CompiledMuGenerationFixture
