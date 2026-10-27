import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourcePruningEnumerationProbeExposureArity
import MicroCFTA.SourcePruningEnumerationNativeArityPrimitives

/-!
# Whole edge-record arity through actual pruning narrowing

The repaired exposure preserves every existing and reconstructed edge key.
The filter retains complete edges. Its final node adds no edge key.
Failed, pending and exhausted reads retain their actual reached heap.
-/
namespace MicroCFTA.SourcePruningEnumerationNarrowArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open MergedSourceExposure (Result)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Key Typing : Type}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Actual narrowAt keeps arity at every returned successful or failed heap. -/
theorem narrowAt_heap
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Constraint → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Constraint) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before) (available : Available before value) (heap : Heap before) :
    Heap (SourcePruningNativeView.narrowAt fits admits fuel key value before).state := by
  have retained := SourcePruningEnumerationProbeExposureArity.nodeEdges_heap fuel value before facts heap available
  unfold SourcePruningNativeView.narrowAt
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      exact SourcePruningEnumerationNativeArityPrimitives.work_heap
        (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits key))) middle
        (by simpa only [actual, Result.state] using retained)
        (SourcePruningEnumerationNativeArityPrimitives.makeNode_fits _ middle)
  | unresolved name after | pending name after | exhausted after =>
      simpa only [actual, Result.state, MergedSourceComparison.Result.state] using retained

/-- Actual outer exemptions and narrowing keep the same whole-heap resource. -/
theorem narrow_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Constraint → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Constraint) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before) (available : Available before value) (heap : Heap before) :
    Heap (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state := by
  cases value with
  | mu => exact heap
  | empty | reference | node | union =>
      unfold SourcePruningOuterNarrow.narrow
      split
      · exact heap
      · exact narrowAt_heap fits admits fuel (holeKey metadata.typing uv) _ before facts available heap

end MicroCFTA.SourcePruningEnumerationNarrowArity
