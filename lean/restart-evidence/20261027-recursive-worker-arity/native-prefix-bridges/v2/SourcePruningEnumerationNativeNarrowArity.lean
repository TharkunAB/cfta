import MicroCFTA.SourcePruningEnumerationProbeExposureArity
import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourceCurrentAllocatedPartialState

/-!
# Arity through the actual selected native narrowing

The row reader retains its exact successful or failed heap.
Filtering adds one node and does not add an edge key.
The enum action and caller publication keep that native endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeNarrowArity
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
variable {Typing Key EnumGuard : Type}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Every actual narrowing outcome retains arity at its own returned heap. -/
theorem narrowAt_heap
    (fits : Key → Symbol → Bool) (admits : Key → Node → Bool) (key : Key)
    (fuel : Nat) (value : Node) (before : State Symbol Constraint)
    (facts : Facts before) (heap : Heap before) (available : Available before value) :
    Heap (SourcePruningNativeView.narrowAt fits admits fuel key value before).state := by
  have retained := SourcePruningEnumerationProbeExposureArity.nodeEdges_heap fuel value before
    facts heap available
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have middleHeap : Heap middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using retained
      simpa only [SourcePruningNativeView.narrowAt, actual, MergedSourceComparison.Result.state] using
        SourcePruningEnumerationArityOrigins.node_heap
          (rows.filter (SourcePruningNativeView.keeps fits admits key)) middle middleHeap
  | unresolved name after | pending pendingKey after | exhausted after =>
      simpa only [SourcePruningNativeView.narrowAt, actual, MergedSourceExposure.Result.state,
        MergedSourceComparison.Result.state] using retained

/-- Typed and Mu skips keep the original heap; other cases use the actual reader. -/
theorem outer_narrow_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (fuel uv : Nat) (value : Node) (before : State Symbol Constraint)
    (facts : Facts before) (heap : Heap before) (available : Available before value) :
    Heap (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state := by
  cases value with
  | mu => exact heap
  | empty | reference | node | union =>
      by_cases typed : uv ∈ metadata.types
      · simpa [SourcePruningOuterNarrow.narrow, typed] using heap
      · simpa [SourcePruningOuterNarrow.narrow, typed] using
          narrowAt_heap fits admits (holeKey metadata.typing uv) fuel _ before facts heap available

/-- Preparing the enum action retains the actual native heap even on failure or absence. -/
theorem prepare_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (value : Node) (before : State Symbol Constraint)
    (facts : Facts before) (heap : Heap before) (available : Available before value) :
    Heap (SourcePruningEnumerationAction.prepare (EnumGuard := EnumGuard) holeKey fits admits metadata
      nativeFuel representativeFuel uv oldHandle scs value before).state := by
  have retained := outer_narrow_heap holeKey fits admits metadata nativeFuel uv value before
    facts heap available
  cases actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value before with
  | failed fault after | done result after =>
      simpa only [SourcePruningEnumerationAction.prepare, actual,
        MergedSourceComparison.Result.state] using retained

/-- The actual caller advance exposes the prepared heap without restoring an older heap. -/
theorem advance_prepare_heap {width : Nat}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (value : Node) (caller : SourceCurrentAllocatedPartialState.State width)
    (facts : Facts caller.checked.native.machine.heap)
    (heap : Heap caller.checked.native.machine.heap)
    (available : Available caller.checked.native.machine.heap value) :
    Heap (SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨(SourcePruningEnumerationAction.prepare (EnumGuard := EnumGuard) holeKey fits admits metadata
          nativeFuel representativeFuel uv oldHandle scs value caller.checked.native.machine.heap).state,
          caller.checked.operations⟩) caller.fourth caller.merge).checked.native.machine.heap :=
  prepare_heap (EnumGuard := EnumGuard) holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs value
    caller.checked.native.machine.heap facts heap available

end MicroCFTA.SourcePruningEnumerationNativeNarrowArity
