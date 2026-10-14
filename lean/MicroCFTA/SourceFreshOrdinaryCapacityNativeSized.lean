import MicroCFTA.SourceFreshOrdinaryNormalizedNativeSized
import MicroCFTA.SourceFreshOrdinaryNativeCompilerCapacity

/-!
# Complete native Sized sequence from actual cache capacity

Checked original annotations give normalized cold rows and ready native state.
Reached source counters derive every native word check. The complete compiler
and all four optimized query fields have the same finite reference sequence.
-/
namespace MicroCFTA.SourceFreshOrdinaryCapacityNativeSized
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Actual normalized construction and reached cache capacities derive all exact native Sized query laws. -/
theorem complete {bits : Nat} {Formula Key : Type}
    [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (expression : InternedNestedConstruction.Syntax (Label Formula) (Constraint Formula))
    (value : Value (Label Formula) (Constraint Formula))
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value source)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) expression)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (domainsValid : Cache.Valid domains)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    let state := initial (bits + 2) (⟨source, domains⟩ : Machine (Label Formula) (Constraint Formula))
    ∃ rows final outer inner,
    ∃ (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
      (supported : Supported rows value)
      (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value)),
      Trace state.machine.heap (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state.machine.heap (fun _ => none) [value] = .done rows final) ∧
      ∃ active : ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) value) key →
          SourceCompactGuards.ActiveOption edge.constraint.equalities,
      let input := SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active
      let native := advance state ⟨final, state.machine.domains⟩
      SourceFreshOrdinaryNativeCompiler.CapacityRanges emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active order native →
      ∃ result after,
        SourceFreshOrdinaryNativeCompiler.Execution emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
          formulas solver order native result after ∧
        SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧
        SourceCyclicRows.compile formulas solver input order = some result ∧
        ∀ output, result = .ok output →
          let states := List.attach (SourceDenseRows.keys (SourceColdSharedRows.table rows (keys final rows) value))
          (SourceSizedDispatcher.optimizedApi output input.root = SourceSizedDispatcher.referenceApi output input.root) ∧
          (∃ fuel, MinimumSize.sweeps output states fuel (fun _ => none) = SourceRowsMinimum.minimumSizes output states ∧
            MinimumSize.sweep output states (SourceRowsMinimum.minimumSizes output states) = SourceRowsMinimum.minimumSizes output states) ∧
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
  let property := fun constraint : Constraint Formula => SourceCompactGuards.ActiveOption constraint.equalities
  have initialHeap : InternedFreshOrdinaryConstraintHeap.Heap property source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap property expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap property) annotations
  obtain ⟨ready, available, valueClosed⟩ := SourceFreshOrdinaryColdNativeTable.constructed
    expression value source built domains domainsValid (bits + 2) emptyGuard conjoin
  obtain ⟨rows, final, outer, inner, trace, stable, finalReady, _, _, _, finalAvailable, supported,
      resident, replayed, children, _, domain, closed, invariant⟩ :=
    SourceFreshOrdinaryColdNativeTable.collect emptyGuard conjoin (initial (bits + 2) ⟨source, domains⟩) ready value available valueClosed
  have inputs : SourceColdSharedRows.Inputs source [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available valueClosed
  have finalHeap := trace.constraint_heap property ready.semantic ready.covered initialHeap inputs
  let active := SourceFreshOrdinaryColdSharedRows.table_constraints property final finalHeap rows resident
    (keys final rows) domain value
  refine ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, active, ?_⟩
  dsimp only
  intro capacity
  have ranges := SourceFreshOrdinaryNativeCompiler.ranges_of_capacity emptyGuard conjoin final rows (keys final rows) value
    domain supported closed [] active order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
    replayed resident children _ invariant capacity
  obtain ⟨result, after, execution, retained, reference⟩ :=
    SourceFreshOrdinaryNativeCompiler.complete_capacity emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
      formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
      _ invariant capacity
  refine ⟨result, after, execution, retained.1, reference, ?_⟩
  intro output success
  cases success
  refine ⟨SourceFreshOrdinaryNativeCompiler.api_record emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
    formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
    _ invariant ranges output after execution, ?_, ?_⟩
  · obtain ⟨fuel, reached, fixed, _⟩ := SourceFreshOrdinaryNativeCompiler.finite_prepass emptyGuard conjoin final rows (keys final rows) value
      domain supported closed [] active formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget
      replayed resident children _ invariant ranges output after execution
    exact ⟨fuel, reached, fixed⟩
  · exact ⟨fun size => SourceFreshOrdinaryNativeCompiler.class_correct emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
      formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
      finalAvailable valueClosed _ invariant ranges output after execution ambient size,
      SourceFreshOrdinaryNativeCompiler.reference_laws emptyGuard conjoin final rows (keys final rows) value domain supported closed [] active
        formulas solver order finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
        finalAvailable valueClosed _ invariant ranges output after execution ambient⟩

end MicroCFTA.SourceFreshOrdinaryCapacityNativeSized
