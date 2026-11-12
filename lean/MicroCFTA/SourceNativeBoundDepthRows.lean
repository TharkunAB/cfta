import MicroCFTA.SourceNativeBoundDepthHeapArity
import MicroCFTA.SourceNativeOrdinaryRows
import MicroCFTA.SourceNativeOrdinaryTermSize
import MicroCFTA.SourceNativeOrdinaryRowsBudget

/-!
# One bounded native copy with finite exact rows and a term-size cap

The original completion receipt supplies the only copied value, heap, and memo.
The row snapshot, size observer, and structural budget use the same returned heap.
This theorem concerns the explicit bounded operation. Default synthesis uses
its separate recursive-marker enumeration.
-/
namespace MicroCFTA.SourceNativeBoundDepthRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepth (Memo Result atHeight)
open SourceNativeReadArityHeap (Heap)
open SourceNativeBoundDepthMeaning (DeepOrdinary)
open InternedGuardedLanguage (meaning)

/-- One original completion receipt has finite exact rows and bounded accepted terms. -/
theorem complete_rows [DecidableEq (EdgeKey Symbol Guard)]
    (depth : Int) (root : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before root) (closed : root.free = []) :
    ∃ cutoff result after memo rowCutoff raw,
      (∀ fuel, cutoff ≤ fuel →
        SourceNativeBoundDepth.boundDepth fuel depth root before = (.done result after, memo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after root ∧ root.free = [] ∧
      Available after result ∧ result.free = [] ∧
      (∀ key value, memo key = some value → Available after value ∧ value.free = []) ∧
      DeepOrdinary result ∧ MergedOrdinaryHeight.height result ≤ (depth + 1).toNat ∧
      (∀ holds ambient term, meaning holds ambient result term ↔
        meaning holds ambient root term ∧ (term.height : Int) ≤ depth + 1) ∧
      SourceNativeReadArityHeap.Heap
        (SourceRecursiveIntersectionSourceProfile.limits before).arity after ∧
      (∀ fuel, rowCutoff ≤ fuel →
        SourceInternedRows.toRows (SourceNativeOrdinaryRows.heap after) fuel
          (SourcePreparedSharedRows.reference result) = some raw) ∧
      (∀ holds ambient term,
        Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw))
          (SourcePreparedSharedRows.encode result) term ↔
          meaning holds ambient root term ∧ (term.height : Int) ≤ depth + 1) ∧
      (∀ holds term,
        Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds raw))
          (SourcePreparedSharedRows.encode result) term →
          NumberedTerms.size term ≤
            SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount 1
              (SourceRecursiveIntersectionSourceProfile.limits before).arity (depth + 1).toNat) ∧
      (∀ holds, Nonempty (GraphBudget.Budget
        (SourceInternedRows.graph (SourceNativeOrdinaryRows.heap after) holds))) := by
  obtain ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, rootAvailable, rootClosed,
      resultAvailable, resultClosed, memoAvailable, ordinary, height, languages, finalHeap⟩ :=
    SourceNativeBoundDepthHeapArity.complete_exact_arity depth root before semantic available closed
  obtain ⟨rowCutoff, raw, rowStable, rowLanguage⟩ :=
    SourceNativeOrdinaryRows.finite after finalSemantic result resultAvailable ordinary
  refine ⟨cutoff, result, after, memo, rowCutoff, raw, stable, finalSemantic, keeps,
    rootAvailable, rootClosed, resultAvailable, resultClosed, memoAvailable, ordinary,
    height, languages, finalHeap, rowStable, ?_, ?_, ?_⟩
  · intro holds ambient term
    exact (rowLanguage holds ambient term).trans (languages holds ambient term)
  · intro holds term accepted
    have native := (rowLanguage holds (fun _ _ => False) term).mp accepted
    have sized := SourceNativeOrdinaryTermSize.accepted_size after finalSemantic
      (SourceRecursiveIntersectionSourceProfile.limits before).arity finalHeap
      result resultAvailable ordinary holds (fun _ _ => False) term native
    exact Nat.le_trans sized
      (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount_mono 1 _ height)

  · intro holds
    exact ⟨SourceNativeOrdinaryRowsBudget.budget after finalSemantic.ready.semantic.1.normal.facts holds⟩

end MicroCFTA.SourceNativeBoundDepthRows
