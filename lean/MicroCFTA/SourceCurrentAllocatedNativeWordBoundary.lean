import MicroCFTA.SourceCurrentAllocatedNativeObservedWords
import MicroCFTA.SourceEqualityNativeDemandNodeShortcut
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Successful native execution does not check word bounds

A closed source constructor allocates an ordinary node with identity one.
Its tagged code is four, which exceeds the safe range at word width two.
An empty-left native request still publishes the key and returns Empty.
The initial physical memo tables are valid and both operands are available.
This example does not assert semantic Ready or an inventory At receipt.
It distinguishes raw execution from a trace that records physical checks.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeWordBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def plain : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) plain [.node [.mk ("leaf", .top) plain []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, root⟩
private def before : Checked 2 :=
  ⟨initial 2 ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.empty⟩
private def control : Control Node := .code (.node request .pure)
private def key : IntersectionFlatMemoKeyDomain.Triple 2 :=
  IntersectionFlatMemoKeyDomain.flatKey 2 IntersectionEmptyDomain.emptyDomain .empty (.node 1)
private def published := (lookupNode 2 request before.native).2
private def running := (demandNode 0 published).2
private def after : Checked 2 := ⟨finishNode 0 .empty running, before.operations⟩

private theorem built_done : built = .done root heap := by cbv

private theorem root_reference : root.referenceOf = .node 1 := by cbv

private theorem heap_facts : InternedNestedFacts.Facts heap :=
  (InternedFreshOrdinaryFacts.closed_verified expression).facts

private theorem root_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done

private theorem operands_ready : NodeReady before.native.machine request :=
  ⟨empty_domain _, empty_available _, root_available⟩

private theorem initial_valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid _ ⟨heap_facts, Cache.empty_valid⟩

private theorem actual_key :
    SourceRecursiveIntersectionMemo.requestKey 2 request.domain request.left request.right = some key := by
  change IntersectionFlatMemoKeyDomain.sourceKey 2 IntersectionEmptyDomain.emptyDomain
    (Value.empty : Node).referenceOf root.referenceOf = some key
  rw [root_reference]
  rfl

private theorem unsafe_key :
    ¬ SourceRecursiveIntersectionMemo.KeySafe 2 request.domain request.left request.right := by
  rintro ⟨_, _, _first, second, _, secondInput, _, secondSafe⟩
  have same : IntersectSchedule.Input.node 1 = second := by
    simpa only [request, root_reference, IntersectionFlatMemoKey.input, Option.some.injEq] using secondInput
  cases same
  simp [IntersectionFlatMemoKey.Safe, IntersectionFlatMemoKey.code] at secondSafe

private theorem actual_done : execute 4 control before = .done .empty after := by
  apply SourceEqualityNativeDemandProvenance.pure_node_complete request before .empty
    (handle := 0) (chosen := published) (current := running)
  · simp [compileNode, SourceRecursiveIntersectionControl.decision,
      SourceRecursiveIntersectionControl.hasEmpty, request, Value.referenceOf]
  · cbv
  · cbv

private theorem unsafe_words : ¬ SourceCurrentAllocatedNativeRequestBounds.Words 2 control := by
  intro words
  exact unsafe_key (words key actual_key)

private theorem no_checked_trace :
    ¬ ∃ fuel, SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before
      (.code (.pure (Value.empty : Node))) after := by
  rintro ⟨fuel, trace⟩
  exact unsafe_words (SourceCurrentAllocatedNativeRequestBounds.WordRanges.current control before
    (SourceCurrentAllocatedNativeObservedWords.trace_wordRanges trace))

/-- Closed available operands and valid empty tables can complete with an unsafe positive-width key. -/
theorem witness :
    ∃ source : Syntax Symbol Guard, ∃ sourceHeap : Heap, ∃ value : Node,
      ∃ original : NodeRequest Symbol Guard, ∃ start finish : Checked 2,
        InternedFreshOrdinaryConstruction.build source [] empty = .done value sourceHeap ∧
        InternedNestedFacts.Facts sourceHeap ∧ value.free = [] ∧ value.referenceOf = .node 1 ∧
        original = ⟨IntersectionEmptyDomain.emptyDomain, .empty, value⟩ ∧
        start.native = initial 2 ⟨sourceHeap, Cache.emptyState⟩ ∧
        SourceCurrentAllocatedNativePhysicalCache.Valid start.native ∧
        SourceEqualityConstraintMemoAllocation.Valid start.operations ∧
        NodeReady start.native.machine original ∧
        (∃ actualKey, SourceRecursiveIntersectionMemo.requestKey 2 original.domain original.left original.right =
          some actualKey) ∧
        ¬ SourceRecursiveIntersectionMemo.KeySafe 2 original.domain original.left original.right ∧
        execute 4 (.code (.node original .pure)) start = .done (Value.empty : Node) finish ∧
        ¬ SourceCurrentAllocatedNativeRequestBounds.Words 2 (.code (.node original (.pure : Node → Code Symbol Guard Node))) ∧
        ¬ SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.node original (.pure : Node → Code Symbol Guard Node))) start ∧
        ¬ ∃ fuel, SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
          (.code (.node original .pure)) start (.code (.pure (Value.empty : Node))) finish := by
  refine ⟨expression, heap, root, request, before, after, built_done, heap_facts, ?_, root_reference,
    rfl, rfl, initial_valid, SourceEqualityConstraintMemoAllocation.empty_valid, operands_ready,
    ⟨key, actual_key⟩, unsafe_key, actual_done, unsafe_words, ?_, no_checked_trace⟩
  · cbv
  · intro inputs
    exact unsafe_words (SourceCurrentAllocatedNativeObservedWords.inputs_words control before inputs)

end MicroCFTA.SourceCurrentAllocatedNativeWordBoundary
