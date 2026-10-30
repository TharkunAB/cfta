import MicroCFTA.SourceCurrentNativeClosedGuardExecute
import MicroCFTA.SourceCurrentAllocatedPartialState

/-!
# Guard heaps at literal enumeration native requests

The incoming and dispatch callers use the same empty-domain request.
Every native outcome retains the guard heap at its returned state.
Physical InputsThrough remains an explicit premise.
The enabled emptiness stage requires a separate composition law.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeRequestGuardHeap
open InternedConstructorTemplates
open SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
variable {width : Nat}

/-- The literal empty-domain request has no allocated edge instruction. -/
theorem request_allocated (before : Checked width) (left right : Node) :
    SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before :=
  fun _ => True.intro

/-- The literal empty-domain request has no guard instruction. -/
theorem request_guards (alphabet : List Guard) (left right : Node) :
    SourceCurrentNativeGuardStep.Fields alphabet
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) :=
  fun _ => True.intro

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every native outcome retains the same closed guard alphabet. -/
theorem execute_heap (alphabet : List Guard)
    (closed : SourceCurrentNativeClosedGuardAlphabet.Closed alphabet)
    (nativeFuel : Nat) (left right : Node) (before : Checked width)
    (good : Good before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    Heap (fun guard => guard ∈ alphabet)
      (SourceEqualityNativeDemand.execute nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state.native.machine.heap :=
  SourceCurrentNativeClosedGuardAlphabet.execute_guard_heap alphabet closed nativeFuel _ before
    good inputs (request_allocated before left right) known (request_guards alphabet left right)

/-- Advancing the caller uses the actual state of every native outcome. -/
theorem advance_heap (alphabet : List Guard)
    (closed : SourceCurrentNativeClosedGuardAlphabet.Closed alphabet)
    (nativeFuel : Nat) (left right : Node) (before : Caller width)
    (good : Good before.checked)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    let actual := SourceEqualityNativeDemand.execute nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked
    Heap (fun guard => guard ∈ alphabet)
      (SourceCurrentAllocatedPartialState.advance before actual.state before.fourth before.merge).checked.native.machine.heap := by
  change Heap (fun guard => guard ∈ alphabet)
    (SourceEqualityNativeDemand.execute nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked).state.native.machine.heap
  exact execute_heap alphabet closed nativeFuel left right before.checked good inputs known

/-- Original normalized literals supply the same finite alphabet at the returned caller. -/
theorem advance_original_heap (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (nativeFuel : Nat) (left right : Node) (before : Caller width)
    (good : Good before.checked)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked)
    (origins : Heap (SourceEqualityConstraintOrigins.Derived literals top conjoin)
      before.checked.native.machine.heap) :
    let actual := SourceEqualityNativeDemand.execute nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked
    Heap (fun guard => guard ∈ SourceCurrentNativeClosedGuardAlphabet.originalAlphabet literals)
      (SourceCurrentAllocatedPartialState.advance before actual.state before.fourth before.merge).checked.native.machine.heap :=
  advance_heap _ (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized)
    nativeFuel left right before good inputs
    (SourceCurrentNativeClosedGuardAlphabet.original_heap literals normalized _ origins)

end MicroCFTA.SourcePruningEnumerationNativeRequestGuardHeap
