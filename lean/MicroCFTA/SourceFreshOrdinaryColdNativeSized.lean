import MicroCFTA.SourceFreshOrdinaryColdNativeTable
import MicroCFTA.SourceFreshOrdinaryNativeCompiler

/-!
# Exact Sized results from actual cold traversal and native compilation

Actual traversal derives the complete finite table and ready native cache.
The compiler then follows its source checks and ordered overlap calls.
Successful results have exact finite classes and both distinct-term inverses.
Only normalized constraints and reached native word checks remain explicit.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdNativeSized
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Actual cold traversal and finite native compilation derive the complete exact Sized sequence. -/
theorem complete {width : Nat} {Formula Key : Type}
    [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (state : SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula))
    (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (value : Value (Label Formula) (Constraint Formula)) (available : Available state.machine.heap value)
    (valueClosed : value.free = [])
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    ∃ rows final outer inner,
    ∃ (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
      (supported : Supported rows value)
      (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value)),
      Trace state.machine.heap (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state.machine.heap (fun _ => none) [value] = .done rows final) ∧
      ∀ active : ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) value) key →
          SourceCompactGuards.ActiveOption edge.constraint.equalities,
      let input := SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active
      let native := advance state ⟨final, state.machine.domains⟩
      SourceFreshOrdinaryNativeCompiler.Ranges emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active order native →
      ∃ result after,
        SourceFreshOrdinaryNativeCompiler.Execution emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
          formulas solver order native result after ∧
        SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧
        SourceCyclicRows.compile formulas solver input order = some result ∧
        ∀ output, result = .ok output →
          (∀ size,
            SourceSizedTableEvaluation.Evaluation output (size + 1) size input.root
              (RecursiveSize.countAt output size input.root) (RecursiveSize.compileAt output size input.root) ∧
            (RecursiveSize.enumerate output size input.root).Nodup ∧
            (∀ term, term ∈ RecursiveSize.enumerate output size input.root ↔
              InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧ RecursiveSize.nodeSize term = size) ∧
            RecursiveSize.countAt output size input.root = (RecursiveSize.enumerate output size input.root).length ∧
            (∀ rank, Decoder.decode (RecursiveSize.compileAt output size input.root) rank =
              (RecursiveSize.enumerate output size input.root)[rank]?) ∧
            SourceSizedReference.classes output size input.root = RecursiveSize.enumerate output size input.root) ∧
          (let classes := fun size => SourceSizedReference.classes output size input.root
           (∀ size, SourceSizedReference.ClassEvaluation output (size + 1) size input.root (classes size)) ∧
           (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
             (SourceSizedQueries.through classes bound).Pairwise (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second) ∧
             ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
               InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧ RecursiveSize.nodeSize term ≤ bound) ∧
           (∀ term, (∃ position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position) ↔
             InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) ∧
           (∀ term position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position ↔
             SourceSizedQueries.unrank classes position = some term)) := by
  obtain ⟨rows, final, outer, inner, trace, stable, finalReady, _, _, _, finalAvailable, supported,
      resident, replayed, children, _, domain, closed, invariant⟩ :=
    SourceFreshOrdinaryColdNativeTable.collect emptyGuard conjoin state ready value available valueClosed
  refine ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, ?_⟩
  intro active
  dsimp only
  intro ranges
  obtain ⟨result, after, execution, retained, reference⟩ :=
    SourceFreshOrdinaryNativeCompiler.complete emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
      formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
      (advance state ⟨final, state.machine.domains⟩) invariant ranges
  refine ⟨result, after, execution, retained.1, reference, ?_⟩
  intro output success
  cases success
  exact ⟨fun size => SourceFreshOrdinaryNativeCompiler.class_correct emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
    formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
    finalAvailable valueClosed _ invariant ranges output after execution ambient size,
    SourceFreshOrdinaryNativeCompiler.reference_laws emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
      formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
      finalAvailable valueClosed _ invariant ranges output after execution ambient⟩

end MicroCFTA.SourceFreshOrdinaryColdNativeSized
