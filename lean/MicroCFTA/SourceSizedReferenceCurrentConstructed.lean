import MicroCFTA.SourceSizedReferenceCurrent
import MicroCFTA.SourceSizedConjunctionCurrentConstructed

/-!
# Current reference values from arbitrary original syntax

Actual construction, selected preparation, and cold collection supply the
reference table and its current structural validation. No caller supplies
a completed table, finite carrier, annotation invariant, or worker bound.
Every successful reference value has the original syntax language at its
exact node count. The classes are finite, complete, distinct, and size ordered.

The result can reject a retained residual guard. It needs no successful
grouped classification. Selection of this route by the mixed dispatcher,
native container correspondence, and total native work remain separate.
-/

namespace MicroCFTA.SourceSizedReferenceCurrentConstructed

open Language SourceGuards SourceObservations SourceSymbolicIndex Std
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)
attribute [local instance] lexOrd

variable {Formula : Type} [DecidableEq Formula] [Ord (Label Formula)]
  [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]

/-- Actual source workers derive the complete current reference value contract. -/
theorem selected_reference
    (expression : Syntax (Label Formula) (Constraint Formula))
    (width : Nat) (emptyGuard : Constraint Formula)
    (conjoin : Constraint Formula → Constraint Formula → Constraint Formula) :
    ∃ value source bound prepared,
    ∃ middle : SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula),
    ∃ rows final outer inner,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value source =
        .done prepared middle.machine.heap) ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin middle ∧
      Trace middle.machine.heap (fun _ => none) [prepared] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner middle.machine.heap
          (fun _ => none) [prepared] = .done rows final) ∧
      (let original := SourceColdSharedRows.sizedTable
          (SourceColdSharedRows.table rows (keys final rows) prepared)
       ∃ valid : SourceFTAValidation.validateRows (encode prepared)
           (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
         .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)),
       let input := SourceSizedStructuralKeys.input original (encode prepared) valid
       ∀ (formulas : Formulas Formula) (solver : Entailment Formula)
         (api : SourceSizedDispatcher.Api (Label Formula)),
         SourceSizedReferenceCurrent.reference original (encode prepared) valid = .ok api →
         (∀ (size : Int) term, term ∈ api.terms size ↔
           InternedGuardedSyntax.evaluate (SourceConstraintEntryRaw.acceptsConstraint formulas solver)
             [] expression term ∧ (RecursiveSize.nodeSize term : Int) = size) ∧
         (∀ size : Nat, SourceSizedReference.ClassEvaluation
           (SourceSizedDispatcher.equalityRows (SourceSizedPreprocessing.sortedRows input))
           (size + 1) size input.root (api.terms (size : Int))) ∧
         (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Nodup ∧
           (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Pairwise
             (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
         (∀ term, (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound) ↔
           InternedGuardedSyntax.evaluate (SourceConstraintEntryRaw.acceptsConstraint formulas solver)
             [] expression term) ∧
         (∀ size rank term,
           (api.rank term).map (fun position => ((position.size : Int), (position.rank : Int))) = some (size, rank) ↔
             api.unrank size rank = some term)) := by
  obtain ⟨value, source, bound, prepared, middle, rows, final, outer, inner,
      built, running, ready, trace, stable, metadata⟩ :=
    SourceSizedConjunctionCurrentConstructed.selected_table expression width emptyGuard conjoin
  obtain ⟨_closed, valid, language, _rejected, _grouped⟩ := metadata
  let original := SourceColdSharedRows.sizedTable
    (SourceColdSharedRows.table rows (keys final rows) prepared)
  refine ⟨value, source, bound, prepared, middle, rows, final, outer, inner,
    built, running, ready, trace, stable, valid, ?_⟩
  dsimp only
  intro formulaOps entailment api success
  obtain ⟨finite, ordered, complete, inverses⟩ :=
    SourceSizedReferenceCurrent.reference_correct formulaOps entailment original (encode prepared) valid api success
  refine ⟨?_, finite, ordered, ?_, inverses⟩
  · intro size term
    exact (SourceSizedReferenceCurrent.reference_signed_exact formulaOps entailment original
      (encode prepared) valid api success size term).trans
        (and_congr_left (fun _ => language formulaOps entailment term))
  · intro term
    exact (complete term).trans (language formulaOps entailment term)

end MicroCFTA.SourceSizedReferenceCurrentConstructed
