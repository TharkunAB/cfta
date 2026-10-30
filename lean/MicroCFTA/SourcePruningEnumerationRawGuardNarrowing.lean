import MicroCFTA.SourceEqualityAnnotationExposure
import MicroCFTA.SourcePruningEnumerationAction

/-!
# Annotation heaps through raw narrowing

Every result retains the input annotation predicate in its reached heap.
The input heap, reader fields, availability, and closure remain explicit.
-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "SemanticHeap" => SourceRecursiveIntersectionSemanticHeap.SemanticHeap
variable {Guard Key : Type}

/-- Every raw narrowing outcome retains the initial edge annotation predicate. -/
theorem narrowAt_heap (P : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : Heap P before) (available : Available before value) (closed : value.free = []) :
    Heap P (narrowAt fits admits fuel key value before).state := by
  have retained := SourceEqualityAnnotationExposure.nodeEdges_heap P fuel value before
    semantic covered heap available closed
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have middleHeap : Heap P middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using retained
      have built := SourceEqualityAnnotationHeap.run P (makeNode (rows.filter (keeps fits admits key)))
        (SourceEqualityAnnotationHeap.makeNode P _) middle middleHeap
      simpa only [narrowAt, exposed, MergedSourceComparison.Result.state] using built
  | pending key after =>
      simpa only [narrowAt, exposed, MergedSourceComparison.Result.state,
        MergedSourceExposure.Result.state] using retained
  | unresolved name after =>
      simpa only [narrowAt, exposed, MergedSourceComparison.Result.state,
        MergedSourceExposure.Result.state] using retained
  | exhausted after =>
      simpa only [narrowAt, exposed, MergedSourceComparison.Result.state,
        MergedSourceExposure.Result.state] using retained

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningOuterNarrow
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "SemanticHeap" => SourceRecursiveIntersectionSemanticHeap.SemanticHeap
variable {Guard Typing Key : Type}

/-- The Mu and typed-position exemptions retain the heap, as does every raw read outcome. -/
theorem narrow_heap (P : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : Heap P before) (available : Available before value) (closed : value.free = []) :
    Heap P (narrow holeKey fits admits metadata fuel uv value before).state := by
  cases value with
  | mu => exact heap
  | empty | reference | node | union =>
      by_cases inside : uv ∈ metadata.types
      · simpa [narrow, inside, MergedSourceComparison.Result.state] using heap
      · simpa [narrow, inside, MergedSourceComparison.Result.state] using
          (SourcePruningNativeView.narrowAt_heap P fits admits fuel
            (holeKey metadata.typing uv) _ before semantic covered heap available closed)

end MicroCFTA.SourcePruningOuterNarrow

namespace MicroCFTA.SourcePruningEnumerationAction
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "SemanticHeap" => SourceRecursiveIntersectionSemanticHeap.SemanticHeap
variable {EnumGuard NativeGuard Typing Key : Type}

/-- Every prepared action or raw failure retains its reached native annotation heap. -/
theorem prepare_heap (P : NativeGuard → Prop) [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (oldValue : Value Symbol NativeGuard) (before : State Symbol NativeGuard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (heap : Heap P before) (available : Available before oldValue) (closed : oldValue.free = []) :
    Heap P (prepare (EnumGuard := EnumGuard) holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue before).state := by
  have retained := SourcePruningOuterNarrow.narrow_heap P holeKey fits admits metadata
    nativeFuel uv oldValue before semantic covered heap available closed
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      nativeFuel uv oldValue before with
  | done result after =>
      simpa only [prepare, narrowed, MergedSourceComparison.Result.state] using retained
  | failed fault after =>
      simpa only [prepare, narrowed, MergedSourceComparison.Result.state] using retained

end MicroCFTA.SourcePruningEnumerationAction
