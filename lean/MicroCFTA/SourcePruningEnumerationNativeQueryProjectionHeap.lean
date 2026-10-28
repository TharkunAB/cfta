import MicroCFTA.SourcePruningEnumerationNativeNodeProjectionHeap
import MicroCFTA.SourcePruningEnumerationNativeBodyTrace

/-!
# Projectability through actual complete checked native queries

The rich body trace exposes the actual checked ready or sentinel branch.
Actual trace-length induction discharges both recursive request families.
Every child-created record belongs to the same returned physical heap.
No unconditional property of raw conjunction or future endpoint is supplied.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeSemanticTraceReadback
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap projectable
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual node lookup and demand do not change any constructor record. -/
theorem node_step_heap (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Checked width) :
    (step (.code (.node request next)) state).state.native.machine.heap = state.native.machine.heap := by
  change (lift state.operations (SourceRecursiveIntersectionNative.step
    SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin
    (.node request next) state.native)).state.native.machine.heap = _
  rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]

private theorem pure_after_step_heap (control : Control A) (before middle after : Checked width)
    (first value : A) (fuel : Nat)
    (one : step control before = .yielded (.code (.pure first)) middle)
    (same : middle.native.machine.heap = before.native.machine.heap)
    (trace : Trace fuel control before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨rest, _count, tail⟩ := after_step fuel control _ before middle after value trace one
  obtain ⟨_zero, _value, retained⟩ := pure_trace rest first value middle after tail.steps
  rw [← retained, same]
  exact heap

private theorem finish_node_heap (handle : Nat) (first value : Value Symbol Guard)
    (before after : Checked width) (fuel : Nat)
    (trace : Trace fuel (.code (.finishNode handle first (.pure first))) before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  exact pure_after_step_heap _ before
    {before with native := SourceRecursiveIntersectionThunks.finishNode handle first before.native}
    after first value fuel rfl rfl trace heap

private theorem finish_edge_heap (handle : Nat) (first value : EdgeValue Symbol Guard)
    (before after : Checked width) (fuel : Nat)
    (trace : Trace fuel (.code (.finishEdge handle first (.pure first))) before (.code (.pure value)) after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  exact pure_after_step_heap _ before
    {before with native := SourceRecursiveIntersectionThunks.finishEdge handle first before.native}
    after first value fuel rfl rfl trace heap

/-- A completed node request consumes only an actual shorter compiled body or a warm hit. -/
theorem node_request_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (bodies : ∀ (count : Nat) (original : NodeRequest Symbol Guard)
      (start final : Checked width) (result : Value Symbol Guard), count < fuel →
      Good start → Heap start.native.machine.heap →
      Trace count (.code (compileNode original)) start (.code (.pure result)) final →
      Heap final.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have unchanged := node_step_heap request (.pure : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) before
      rw [show step (.code (.node request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          cases selection with
          | direct original =>
              simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, lift, code_bind_pure] at one
              cases one
              exact bodies count original _ after value (Nat.lt_succ_self _) currentGood currentHeap tail
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      obtain ⟨_zero, _same, retained⟩ := pure_trace count result value _ after tail.steps
                      rw [← retained]
                      exact currentHeap
                  | evaluate original =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      obtain ⟨inner, outer, result, middle, total, body, finish⟩ :=
                        bind_inverse count (.code (compileNode original))
                          (fun result => .finishNode handle result (.pure result)) _ after value tail
                      have bodyHeap := bodies inner original _ middle result (by omega) currentGood currentHeap body
                      exact finish_node_heap handle result value middle after outer finish bodyHeap

/-- A completed edge request consumes only its actual shorter checked body or a warm hit. -/
theorem edge_request_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after)
    (bodies : ∀ (count : Nat) (original : EdgeRequest Symbol Guard)
      (start final : Checked width) (result : EdgeValue Symbol Guard), count < fuel →
      Good start → EdgeReady start.native.machine original → Heap start.native.machine.heap →
      Trace count (.edgeBody original .pure) start (.code (.pure result)) final →
      Heap final.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have currentFields := checked.2.2.2.2.2
      rw [one] at currentFields
      have unchanged := SourceEqualityNativeDemandHeap.step_edge_heap request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) before
      rw [show step (.code (.edge request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
              cases observation with
              | absent | busy =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
              | ready result =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  obtain ⟨_zero, _same, retained⟩ := pure_trace count result value _ after tail.steps
                  rw [← retained]
                  exact currentHeap
              | evaluate original =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  obtain ⟨inner, outer, result, middle, total, body, finish⟩ :=
                    bind_inverse count (.edgeBody original .pure)
                      (fun result => .finishEdge handle result (.pure result)) _ after value tail
                  have bodyHeap := bodies inner original _ middle result (by omega) currentGood currentFields.1 currentHeap body
                  exact finish_edge_heap handle result value middle after outer finish bodyHeap

end MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap

namespace MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap projectable
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- The actual ready prefix supplies a successful projection of the emitted guard. -/
theorem ready_projectable
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second combined : Allocated) (leftArity rightArity : Nat)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (firstReady : SourceEqualityConstraintAllocation.Ready operations.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready operations.constraints second.stored)
    (observed : (SourceEqualityIntersectionEdgeAllocation.run le first second
      leftArity rightArity operations).1 = .ok (.ready combined)) :
    SourcePruningEnumerationConstraint.project (SourceEqualityConjoinAllocation.readback combined) ≠ none := by
  obtain ⟨branch, literal, sourceSame, _prefixValid, _growth, _ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second leftArity rightArity
      operations valid firstReady secondReady
  have branchSame : branch = .ready combined := Except.ok.inj (literal.symm.trans observed)
  subst branch
  have accepted : SourceEqualityMkEdgeAllocation.accepted
      (SourceEqualityConjoinAllocation.readback combined) leftArity = true := by
    change SourceEqualityIntersectionEdgeAllocation.Branch.ready
      (SourceEqualityConjoinAllocation.readback combined) = _ at sourceSame
    unfold SourceEqualityIntersectionEdgeAllocation.source at sourceSame
    split at sourceSame
    next _mismatch => cases sourceSame
    next _matched =>
      dsimp only at sourceSame
      split at sourceSame
      next kept =>
        have readbackSame := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj sourceSame
        rw [readbackSame]
        exact kept
      next _rejected => cases sourceSame
  exact SourcePruningEnumerationCheckedProjection.accepted_projectable
    (SourceEqualityConjoinAllocation.readback combined) leftArity accepted

/-- Actual shorter node calls derive projectability for all records in the completed body heap. -/
theorem body_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (limit : Nat)
    (calls : ∀ (request : NodeRequest Symbol Guard) (count : Nat), count ≤ limit →
      ∀ (start final : Checked width) (result : Value Symbol Guard), Good start →
        Heap start.native.machine.heap →
        Trace count (.code (requestNode request.domain request.left request.right)) start (.code (.pure result)) final →
        Heap final.native.machine.heap)
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (value : EdgeValue Symbol Guard) (bounded : fuel ≤ limit)
    (valid : Good before) (inputs : EdgeReady before.native.machine request)
    (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.edgeBody request .pure) before (.code (.pure value)) after) :
    Heap after.native.machine.heap := by
  obtain ⟨code, started, rest, total, _one, nativeSame, startedGood, _startedFields,
      _tail, _afterGood, branch⟩ :=
    SourcePruningEnumerationNativeBodyTrace.body_observation_rich request fuel before after value trace valid inputs
  have startedHeap : Heap started.native.machine.heap := by rw [nativeSame]; exact heap
  rcases branch with ⟨_codeSame, _size, _operands, _valueSame, afterSame⟩ |
      ⟨first, second, combined, values, middle, childFuel, left, right, accepted,
        _codeSame, _startedSame, counted, walked, _middleGood, _operands, _valueSame, afterSame, _lengthSame⟩
  · rw [afterSame]
    have sentinel : projectable (top : Guard) := by
      change (some ([], none) : Option (List EqualityTrie.Trie × Option Guard)) ≠ none
      intro impossible
      cases impossible
    exact SourceEqualityAnnotationHeap.run projectable _
      (SourceEqualityAnnotationHeap.makeEdge projectable _ top [.empty] sentinel)
      started.native.machine.heap startedHeap
  · have childHeap := walk_heap limit
      (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
      (fun pair count bound start final result good current actual =>
        calls ⟨request.domain, pair.1, pair.2⟩ count bound start final result good current actual)
      (fun _ _ => fun _ => trivial)
      (request.left.children.zip request.right.children) values started middle childFuel
      (by omega) startedGood startedHeap walked
    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
      (valid.fields _ _ inputs.2.1).1 first left).1
    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
      (valid.fields _ _ inputs.2.2).1 second right).1
    have checked := ready_projectable
      GuardStructuralOrder.le first second combined request.left.children.length request.right.children.length
      before.operations valid.operations firstReady secondReady accepted
    rw [afterSame]
    exact SourceEqualityAnnotationHeap.run projectable _
      (SourceEqualityAnnotationHeap.makeEdge projectable request.left.entry.key.symbol
        (SourceEqualityConjoinAllocation.readback combined) values checked)
      middle.native.machine.heap childHeap

end MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap

namespace MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap projectable
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem query_heaps (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard),
      Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after →
      Heap after.native.machine.heap) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before after : Checked width) (value : EdgeValue Symbol Guard),
      Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after →
      Heap after.native.machine.heap) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      constructor
      · intro request before after value valid heap trace
        apply SourcePruningEnumerationNativeQueryProjectionHeap.node_request_heap request before after value fuel valid heap trace
        intro count original start final result smaller good current actual
        apply compileNode_heap count
          (fun requested used bounded initial output answer checked origin called =>
            (ih used (by omega)).1 requested initial output answer checked origin called)
          (fun requested used bounded initial output answer checked origin called =>
            (ih used (by omega)).2 requested initial output answer checked origin called)
          original start final result count (Nat.le_refl _) good current actual
      · intro request before after value valid heap trace
        apply SourcePruningEnumerationNativeQueryProjectionHeap.edge_request_heap request before after value fuel valid heap trace
        intro count original start final result smaller good ready current actual
        apply body_heap count
          (fun requested used bounded initial output answer checked origin called =>
            (ih used (by omega)).1 requested initial output answer checked origin called)
          original count start final result (Nat.le_refl _) good ready current actual

/-- Every actual complete native node query retains projectability of its entire returned edge-record heap. -/
theorem node_query_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Heap after.native.machine.heap :=
  (query_heaps fuel).1 request before after value valid heap trace

/-- Every actual complete native edge query retains projectability of all old and newly created edge records. -/
theorem edge_query_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after) :
    Heap after.native.machine.heap :=
  (query_heaps fuel).2 request before after value valid heap trace

/-- Every returned edge memo cell after a native node query projects from its actual resident record. -/
theorem node_query_edge_memo_projectable (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (handle : Nat) (original : EdgeRequest Symbol Guard) (edge : EdgeValue Symbol Guard)
    (stored : after.native.edges.cells handle = some ⟨original, .returned edge⟩) :
    SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none := by
  have afterHeap := node_query_heap request before after value fuel valid heap trace
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace valid (fun _ => trivial)
  have resident := (reached.1.native.edges.checked handle _ stored).2
  exact afterHeap edge.entry.key edge resident

end MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap
