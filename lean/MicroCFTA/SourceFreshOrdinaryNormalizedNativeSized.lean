import MicroCFTA.SourceFreshOrdinaryColdNativeSized
import MicroCFTA.SourceFreshOrdinaryColdConstraintHeap

/-!
# Exact native Sized queries from normalized source construction

Input annotations establish the constraint invariant at construction time.
Actual stored substitution and cold traversal derive normalized final rows.
The resulting native compiler has the same exact finite reference sequence.
No rowwise normalization certificate or final-cache metadata is supplied.
-/
namespace MicroCFTA.SourceFreshOrdinaryNormalizedNativeSized
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Actual normalized construction, cold traversal, and native compilation derive the complete exact Sized sequence. -/
theorem complete {width : Nat} {Formula Key : Type}
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
    let state := initial width (⟨source, domains⟩ : Machine (Label Formula) (Constraint Formula))
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
  let property := fun constraint : Constraint Formula => SourceCompactGuards.ActiveOption constraint.equalities
  have initialHeap : InternedFreshOrdinaryConstraintHeap.Heap property source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap property expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap property) annotations
  obtain ⟨ready, available, valueClosed⟩ := SourceFreshOrdinaryColdNativeTable.constructed
    expression value source built domains domainsValid width emptyGuard conjoin
  obtain ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, finish⟩ :=
    SourceFreshOrdinaryColdNativeSized.complete emptyGuard conjoin (initial width ⟨source, domains⟩) ready
      value available valueClosed formulas solver order ambient
  have inputs : SourceColdSharedRows.Inputs source [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available valueClosed
  have finalHeap := trace.constraint_heap property ready.semantic ready.covered initialHeap inputs
  obtain ⟨_, _, _, _, _, resident⟩ := trace.correct ready.semantic ready.covered inputs
    (by intro identity edges absent; cases absent)
  let active := SourceFreshOrdinaryColdSharedRows.table_constraints property final finalHeap rows resident
    (keys final rows) domain value
  exact ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, active, finish active⟩

end MicroCFTA.SourceFreshOrdinaryNormalizedNativeSized
