import MicroCFTA.SourceCurrentConjunctionDemandExecution
import MicroCFTA.SourceCurrentConjunctionTuplePullHeapEffects
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects
import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
import MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome
import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceCurrentUnionNormalConjunction
import MicroCFTA.SourceCurrentConjunctionGuard
import MicroCFTA.SourcePruningEnumerationConjunctionArity

/-!
# Concrete heap invariants through actual demand admission

Union normality needs only its original heap invariant. Physical annotation
preservation includes all sampling and requirement faults. Causal guard
observations and arity hold on every sampling outcome. Their admission
laws use the same successful allocation premise as the older graph laws.
No law assumes a future heap annotation or an exposure of unread operands.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandAnnotations
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentRequiredUnionNormal (UnionNormal)

section GenericProofs
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem bind_heap {A B : Type} (property : Heap → Prop)
    (first : Outcome Symbol Formula A)
    (next : A → Physical Symbol Formula → Outcome Symbol Formula B)
    (known : property first.state.heap)
    (later : ∀ value after, first = .done value after → property after.heap →
      property (next value after).state.heap) : property (first.bind next).state.heap := by
  cases first with
  | failed => exact known
  | done value after => exact later value after rfl known

private theorem sample_heap (property : Heap → Prop) (h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (semantic : SemanticReady before.heap)
    (costs : CostHeap before.heap) (available : Values before.heap nodes) (known : property before.heap)
    (read : ∀ node heap, SemanticReady heap → Available heap node → property heap →
      property (MergedFreshOrdinaryExposure.nodeEdges h node heap).state) :
    property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap := by
  let invariant (heap : Heap) := SemanticReady heap ∧ CostHeap heap ∧ Values heap nodes ∧ property heap
  have retained := SourceCurrentConjunctionTuplePullHeapEffects.sample_preserves invariant h budget nodes before
    ⟨semantic, costs, available, known⟩ (by
      intro heap node member current
      have input := current.2.2.1 node member
      have checked := SourceEqualityExposureCosts.nodeEdges_verified h node heap current.1 current.2.1 input
      exact ⟨checked.semantic, checked.costs,
        fun value present => checked.keeps.available value (current.2.2.1 value present),
        read node heap current.1 input current.2.2.2⟩)
  exact retained.2.2.2

/-- Every sampling outcome retains union normality without readiness premises. -/
theorem sample_unionNormal (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap :=
  SourceCurrentConjunctionTuplePullHeapEffects.sample_preserves UnionNormal h budget nodes before normal
    (fun heap node _ current => SourceCurrentRequiredUnionNormalRead.nodeEdges h node heap current)

/-- Every demand-admission outcome retains the original weak union invariant. -/
theorem run_unionNormal (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionDemandAdmission.run p h budget nodes before).state.heap := by
  unfold SourceCurrentConjunctionDemandAdmission.run
  apply bind_heap UnionNormal _ _ (sample_unionNormal h budget nodes before normal)
  intro sampled middle _ current
  cases sampled with
  | overflow => exact current
  | fit tuples =>
      cases tuples with
      | nil => exact current
      | cons first rest =>
          exact bind_heap UnionNormal _ _
            (SourceCurrentUnionNormalConjunction.tuples p h (first :: rest) middle current)
            (fun _ _ _ retained => retained)

/-- Actual demanded reads retain arbitrary physical annotations on every outcome. -/
theorem sample_annotation_heap (annotation : Guard → Prop) (h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (semantic : SemanticReady before.heap)
    (costs : CostHeap before.heap) (available : Values before.heap nodes)
    (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation
      (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap :=
  sample_heap _ h budget nodes before semantic costs available known
    (fun node heap current input retained =>
      SourceCurrentOpenExposureFields.nodeEdges_heap annotation h node heap current retained input)

/-- All sampling and requirement outcomes retain the physical annotation predicate. -/
theorem run_annotation_heap (annotation : Guard → Prop) (p h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation
      (SourceCurrentConjunctionDemandAdmission.run p h budget nodes before).state.heap := by
  have first := sample_annotation_heap annotation h budget nodes before ready.semantic ready.costs available known
  have physical := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  unfold SourceCurrentConjunctionDemandAdmission.run
  apply bind_heap _ _ _ first
  intro sampled middle actual current
  have kept : Effects before middle := by simpa only [actual, Outcome.state] using physical.1
  have resident := physical.2 sampled middle actual
  cases sampled with
  | overflow => exact current
  | fit tuples =>
      cases tuples with
      | nil => exact current
      | cons first rest =>
          have closedRows := SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle
            (first :: rest) actual ready available closed
          have shapes := SourceCurrentConjunctionTuplePullShapes.sample_fit h budget nodes before middle
            (first :: rest) actual
          have later := SourceCurrentConjunctionRowsAnnotationOutcome.tuples_heap annotation p h
            (first :: rest) middle kept.ready resident closedRows
            (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple (shapes tuple member).2.1)
            current
          exact bind_heap _ _ _ later (fun _ _ _ retained => retained)

/-- Every actual sampling outcome retains the causal Mu guard observations. -/
theorem sample_guard_heap (annotation : Guard → Prop) (h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (semantic : SemanticReady before.heap)
    (costs : CostHeap before.heap) (available : Values before.heap nodes)
    (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation
      (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap :=
  sample_heap _ h budget nodes before semantic costs available known
    (fun node heap current input retained =>
      SourceCurrentConstrainedCapMergeGuardEffects.nodeEdges_heap annotation h node heap current retained input)

/-- Every completed admission graph retains the original causal guard heap. -/
theorem admission_guard_heap {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (annotation : Guard → Prop)
    (actual : SourceCurrentConjunctionDemandExecution.Admission budget nodes before result after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation after.heap := by
  cases actual with
  | @overflow h budget nodes before middle tuples cursor sampled =>
      simpa only [sampled, Outcome.state] using
        sample_guard_heap annotation h budget nodes before ready.semantic ready.costs available known
  | @zero h budget nodes before middle sampled =>
      simpa only [sampled, Outcome.state] using
        sample_guard_heap annotation h budget nodes before ready.semantic ready.costs available known
  | @positive h budget nodes before middle after first rest requirements sampled allocated =>
      have physical := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
      have kept : Effects before middle := by simpa only [sampled, Outcome.state] using physical.1
      have resident := physical.2 (.fit (first :: rest)) middle sampled
      have closedRows := SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle
        (first :: rest) sampled ready available closed
      have current := sample_guard_heap annotation h budget nodes before ready.semantic ready.costs available known
      exact SourceCurrentConjunctionGuard.tuples annotation allocated kept.ready resident closedRows
        (by simpa only [sampled, Outcome.state] using current)
end GenericProofs

section ArityProofs
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every demanded sample outcome retains the whole edge-record arity invariant. -/
theorem sample_arity_heap (h budget : Nat) (nodes : List Node)
    (before : Physical Symbol FullSyntax.Formula) (semantic : SemanticReady before.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.heap) (available : Values before.heap nodes)
    (known : SourcePruningEnumerationArityOrigins.Heap before.heap) :
    SourcePruningEnumerationArityOrigins.Heap
      (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap :=
  sample_heap _ h budget nodes before semantic costs available known
    (fun node heap current input retained => SourcePruningEnumerationProbeExposureArity.nodeEdges_heap
      h node heap current.ready.semantic.1.normal.facts retained input)

/-- Every completed admission graph preserves arity from the original heap. -/
theorem admission_arity_heap {budget : Nat} {nodes : List Node}
    {before after : Physical Symbol FullSyntax.Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionDemandExecution.Admission budget nodes before result after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (known : SourcePruningEnumerationArityOrigins.Heap before.heap) :
    SourcePruningEnumerationArityOrigins.Heap after.heap := by
  cases actual with
  | @overflow h budget nodes before middle tuples cursor sampled =>
      simpa only [sampled, Outcome.state] using
        sample_arity_heap h budget nodes before ready.semantic ready.costs available known
  | @zero h budget nodes before middle sampled =>
      simpa only [sampled, Outcome.state] using
        sample_arity_heap h budget nodes before ready.semantic ready.costs available known
  | @positive h budget nodes before middle after first rest requirements sampled allocated =>
      have physical := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
      have kept : Effects before middle := by simpa only [sampled, Outcome.state] using physical.1
      have resident := physical.2 (.fit (first :: rest)) middle sampled
      have closedRows := SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle
        (first :: rest) sampled ready available closed
      have current := sample_arity_heap h budget nodes before ready.semantic ready.costs available known
      exact SourcePruningEnumerationConjunctionArity.tuples_heap allocated kept.ready resident closedRows
        (by simpa only [sampled, Outcome.state] using current)
end ArityProofs

end MicroCFTA.SourceCurrentConjunctionDemandAnnotations
