import MicroCFTA.SourcePruningEnumerationNativeBodyPrefixArity
import MicroCFTA.SourcePruningEnumerationNativeRequestPrefixArity

/-!
# Arity at every actual yielded native query prefix

Induction uses the actual number of yielded instructions.
Both recursive call families retain their full current heap.
No successful future return is required.
-/
namespace MicroCFTA.SourcePruningEnumerationNativePrefixArity
open InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourcePruningEnumerationArityOrigins (Fits Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem query_prefix_heaps (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before after : Checked width)
      (remaining : Control (Value Symbol Guard)), Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after →
      Heap after.native.machine.heap) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before after : Checked width)
      (remaining : Control (EdgeValue Symbol Guard)), Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after →
      Heap after.native.machine.heap) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      constructor
      · intro request before after remaining valid heap trace
        apply node_request_prefix_heap request before after remaining fuel valid heap trace
        intro count original start final rest smaller good current actual
        apply compileNode_prefix_heap count
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).1 requested initial output resume checked origin called)
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).2 requested initial output resume checked origin called)
          original start final rest count (Nat.le_refl _) good current actual
      · intro request before after remaining valid heap trace
        apply edge_request_prefix_heap request before after remaining fuel valid heap trace
        intro count original start final rest smaller good ready current actual
        apply body_prefix_heap count
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).1 requested initial output resume checked origin called)
          original count start final rest (Nat.le_refl _) good ready current actual

/-- Every actual node-query prefix retains arity for all old and newly created edge records. -/
theorem node_query_prefix_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after) :
    Heap after.native.machine.heap :=
  (query_prefix_heaps fuel).1 request before after remaining valid heap trace

/-- Every actual edge-query prefix retains the complete arity heap without a future return. -/
theorem edge_query_prefix_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after) :
    Heap after.native.machine.heap :=
  (query_prefix_heaps fuel).2 request before after remaining valid heap trace

/-- Completed edge memo cells retain arity at every actual node-query prefix endpoint. -/
theorem node_prefix_edge_memo_fits (request : NodeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after)
    (handle : Nat) (original : EdgeRequest Symbol Guard) (edge : EdgeValue Symbol Guard)
    (stored : after.native.edges.cells handle = some ⟨original, .returned edge⟩) :
    Fits edge.entry.key.constraint edge.children.length := by
  have afterHeap := node_query_prefix_heap request before after remaining fuel valid heap trace
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace valid (fun _ => trivial)
  have resident := (reached.1.native.edges.checked handle _ stored).2
  exact afterHeap.edge _ reached.1.heap.semantic.1.normal.facts.coherent edge resident

end MicroCFTA.SourcePruningEnumerationNativePrefixArity
